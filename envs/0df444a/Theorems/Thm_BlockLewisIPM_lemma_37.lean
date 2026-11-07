-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_37
-- name    : BlockLewisIPM.lemma_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:30.742568+00:00
-- url     : https://prove2.me/theorems/78e40fd7-b5c4-4449-b630-f5e6af97cbea
-- title:
--   Lemma 37 — approximate feasibility after a short step (corrected: spectral approximations at $c_0\alpha$)
-- statement:
--   Consider one call of Algorithm 1 at an $\epsilon$-centered triplet $(x,s,\rho)$, with an $\alpha$-approximation $(\bar x,\bar\tau)$ of $(x,\tau)$, $\tau=\tau(x)$, and a valid sampling $R$. There is an absolute $c_0\in(0,1]$ such that, if $\bar H\approx_{c_0\alpha}H$ and item 5 of Definition 19 holds at $c_0\alpha$ with high probability, then with high probability
--
--   $$\|A^\top x^{(\mathrm{new})}-b\|_{H^{-1}}\le\frac{\alpha\beta}{2C_{\mathrm{norm}}},$$
--
--   where $H=A^\top\bar T^{-1}\nabla^2\Phi(\bar x)^{-1}A$. So approximate primal feasibility survives each step.
--
--   Differences from the source:
--   - correction: H̄ ≈_α H and item 5 at α → H̄ ≈_{c₀α} H and item 5 at c₀α, for an absolute c₀ > 0; reason: the proof ends "We choose a sufficiently small constant hidden inside O(α) ratio in the spectral approximation". Counterexample as printed: m = n = 2, d = 1, K_i = [−1,1], ϕ_i = −log(1 − x²), A = (1,1)⊤, b = c = 0, x = s = 0, µ = µ̄ = 0, so every h is a maximizer, R = I, H̄ = e^α H, g = −βt(1,1) with t = 1/(1 + √2 C_norm); then the norm is (1 − e^{−α})√2 βt > αβ/(2C_norm)
--   - reading: (x̄, τ̄) an α-approximation (the lemma as printed) → also (x, s, ρ) ϵ-centered with the ϵ of Algorithm 1 and all lines of Algorithm 1 hold; reason: §4.2, p.22: "We will suppose (x, s, ρ) is ϵ-central for the rest of the section"
--   - reading: constants hidden in ≲ and O(·), C "sufficiently large" (p.10), C_Var "sufficiently large" (Definition 19) → ∃ K₀ C₀ for each bound N on block sizes, ∀ C ≥ C₀, ∃ a C_Var threshold depending on C only, besides C_Var ≥ C_norm; reason: §3.1 puts C above the hidden constants, Algorithm 1 fixes β without n_i, n_i β ≲ 1 (p.24) needs N, and Definition 19 asks C_Var ≥ C_norm and "a sufficiently large constant"
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 37, p.37, and its proof, pp.75–76

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 37**, p.37 (corrected: C5). Zhang, Wright, *A Fast Lewis-weight Interior Point Method for
Linear Optimization over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** `H̄ ≈_{c₀α} H` and item 5 of Definition 19 at `c₀α` carry the proof's last sentence
(p.76): "We choose a sufficiently small constant hidden inside `O(α)` ratio in the spectral approximation
to ensure this." With `H̄ ≈_α H` alone the printed bound fails: take `m = n = 2`, `d = 1`, `K_i = [-1,1]`,
`ϕ_i = -log(1 - x²)`, `A = (1,1)⊤`, `b = 0`, `c = 0`, `x = s = 0`, so `µ = µ̄ = 0`, every `h` is a
maximizer, `R = I`, `H̄ = e^α H`, `g = -β t (1,1)` with `t = 1/(1 + √2 C_norm)`. Then
`‖A⊤x^(new) - b‖_{H⁻¹} = (1 - e^{-α}) √2 β t > αβ/(2C_norm)`. The norm is at `x̄` and `τ̄` (`H`). -/
theorem lemma_37 (N : ℕ) : ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ 10000 ≤ C₀ ∧ ∀ C ≥ C₀, ∃ Cv₀ : ℝ,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.Standing N →
    ∀ Cvar ≥ Cv₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ι → ℝ)
      (D : I.StepData), IsStepCall (I.par C) Cvar D μ R →
    let P := I.par C
    ApproxEq (c₀ * P.α) D.Hb D.H →
    Whp μ P.m (fun ω => I.SpectralEvent (c₀ * P.α) D.xb D.τb (R ω)) →
    Whp μ P.m (fun ω =>
      wNorm D.H⁻¹ (I.Aᵀ *ᵥ D.xNew (R ω) - I.b) ≤ P.α * P.β / (2 * P.Cnorm)) := by sorry

end BlockLewisIPM
