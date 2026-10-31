-- Prove2me | Theorems.Thm_BlockchainNV_theorem_1
-- name    : BlockchainNV.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:22.181924+00:00
-- url     : https://prove2.me/theorems/356445a9-136a-47aa-9967-6f720a182769
-- title:
--   Theorem 1 — the value of freshness transparency is $V=(p-s)(\sigma_D-\sigma)\varphi(z^*)>0$
-- statement:
--   Assume the base model of §2: unit retail price $p$, wholesale price $w$ and salvage value $s$ with $w > 0$, $p > w$, $s < w$; demand $D = \lambda + \beta X + \varepsilon$ with $\lambda > 0$, $\beta > 0$, where the freshness state $X \sim N(\mu_X, \sigma_X^2)$ and the demand shock $\varepsilon \sim N(0, \sigma^2)$ are independent, $\sigma_X > 0$, $\sigma > 0$. Let $r = (p-w)/(p-s)$, $z^* = \Phi^{-1}(r)$, $\sigma_D = \sqrt{\beta^2\sigma_X^2 + \sigma^2}$, and let $\varphi$ be the standard normal density.
--
--   The blockchain retailer observes $X$ before ordering and earns the conditional optimum $\Pi^*(X)$; the traditional retailer knows only the distribution of $X$ and earns $\Pi^*_o$, the optimal expected profit against $D$. Then
--
--   1. $\mathbb E_X[\Pi^*(X)] = (p-w)(\lambda + \beta\mu_X) - (p-s)\,\sigma\,\varphi(z^*)$;
--   2. $\Pi^*_o = (p-w)(\lambda + \beta\mu_X) - (p-s)\,\sigma_D\,\varphi(z^*)$;
--   3. the expected profit increase brought by blockchain-enabled freshness transparency is
--   $$
--   V := \mathbb E_X[\Pi^*(X)] - \Pi^*_o = (p-s)(\sigma_D - \sigma)\,\varphi(z^*);
--   $$
--   4. $V > 0$.
--
--   The theorem quantifies the value of knowing the freshness state before ordering: it is proportional to the reduction $\sigma_D - \sigma$ of the demand uncertainty that the retailer faces.
--
--   Differences from the source:
--   - encoding: z* = Φ^{-1}(r), r = (p − w)/(p − s) → a real z with cdf (gaussianReal 0 1) z = (p − w)/(p − s); reason: Φ is a strictly increasing continuous bijection ℝ → (0,1) and r ∈ (0,1), so the hypothesis determines z = Φ^{-1}(r); such a z exists (proved in the sanity file).
--   - encoding: X ∼ N(µ_X, σ_X²) and ε ∼ N(0, σ²) independent → random variables X, ε on a measurable space (Ω, P) with HasLaw X (gaussianReal µ_X (σ_X²).toNNReal) P, HasLaw ε (gaussianReal 0 (σ²).toNNReal) P and IndepFun X ε P (IsModel); reason: the same model; HasLaw makes P a probability measure, and toNNReal is the identity on a square.
--   - reading: standard deviations σ_X and σ, positivity not printed → 0 < σ_X and 0 < σ (fields of Params); reason: the paper divides by σ (Lemma EC.1, Case 1) and by σ_X (p.13); with σ_X = 0 or σ = 0 the normal laws are degenerate and the formulas (Φ-arguments divided by σ) are undefined.
--   - reading: the optimal order quantity / optimal expected profit, range of q unstated → maximum and supremum over all order quantities q ∈ ℝ; reason: the base model of §2 restricts neither q nor demand to be nonnegative (normal demand), and q*(x) = λ + βx + σz* is negative for small x; nonnegative demand appears only in the §5 extensions.
--   - encoding: the demand distribution conditional on X = x, D_x ∼ N(λ + βx, σ²) → the law of ω ↦ λ + βx + ε(ω) under P; reason: X and ε are independent, so the conditional law of D = λ + βX + ε given X = x is the law of λ + βx + ε.
--   - encoding: E_X[Π*(X)] and Π*_o → ∫ ω, PiStar θ P ε (X ω) ∂P and PiStarO θ P X ε, both suprema (sSup) over q ∈ ℝ; reason: the expectation over X of the conditional optimum and the optimum against D.
-- source:
--   Keskin, Li, Song, The Blockchain Newsvendor: Value of Freshness Transparency and Smart Contracts, Management Science (2024), doi:10.1287/mnsc.2021.02949, Theorem 1, p.8 (PDF p.8); proof, pp.ec11–ec12 (PDF pp.39–40)

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel
import Definitions.Def_BlockchainNV_PiStar
import Definitions.Def_BlockchainNV_PiStarO

open MeasureTheory ProbabilityTheory

namespace BlockchainNV

/-- Keskin, Li, Song, *The Blockchain Newsvendor: Value of Freshness Transparency and Smart
Contracts*, Management Science (2024), doi:10.1287/mnsc.2021.02949, Theorem 1, p.8 (PDF p.8). "The blockchain retailer's optimal expected profit is
`E_X[Π*(X)] = (p − w)(λ + βµ_X) − (p − s)σφ(z*)`, and the traditional retailer's optimal expected
profit is `Π*_o = (p − w)(λ + βµ_X) − (p − s)σ_D φ(z*)`. Thus, the expected profit increase brought
by blockchain-enabled freshness transparency is `V := E_X[Π*(X)] − Π*_o = (p − s)(σ_D − σ)φ(z*) > 0`."
Here `σ_D = √(β²σ_X² + σ²)`, `r = (p − w)/(p − s)` and `z* = Φ^{-1}(r)`.

**Formalization Note.** The model (§2, p.7) is `Params` (with `σ_X > 0`, `σ > 0`) and `IsModel`
(independent Gaussian `X`, `ε` on a probability space). `Π*(x)` and `Π*_o` are suprema over all
order quantities `q ∈ ℝ` (`PiStar`, `PiStarO`); `E_X[Π*(X)]` is `∫ ω, Π*(X ω) ∂P`.
`z* = Φ^{-1}(r)` is a real `z` with `Φ(z) = r`; `φ = gaussianPDFReal 0 1`. -/
theorem theorem_1 (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = (θ.p - θ.w) / (θ.p - θ.s)) :
    let σD : ℝ := Real.sqrt (θ.beta ^ 2 * θ.sigmaX ^ 2 + θ.sigma ^ 2)
    ∫ ω, PiStar θ P ε (X ω) ∂P =
        (θ.p - θ.w) * (θ.lam + θ.beta * θ.muX) - (θ.p - θ.s) * θ.sigma * gaussianPDFReal 0 1 z ∧
      PiStarO θ P X ε =
        (θ.p - θ.w) * (θ.lam + θ.beta * θ.muX) - (θ.p - θ.s) * σD * gaussianPDFReal 0 1 z ∧
      (∫ ω, PiStar θ P ε (X ω) ∂P) - PiStarO θ P X ε =
        (θ.p - θ.s) * (σD - θ.sigma) * gaussianPDFReal 0 1 z ∧
      0 < (θ.p - θ.s) * (σD - θ.sigma) * gaussianPDFReal 0 1 z := by sorry

end BlockchainNV
