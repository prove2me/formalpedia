-- Prove2me | Theorems.Thm_CoVaRMC_Batching_Supplement_theorem_5
-- name    : CoVaRMC.Batching.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:15:52.607381+00:00
-- url     : https://prove2.me/theorems/3643b6f8-e5c2-49ba-8ec3-c32ea7c699c2
-- title:
--   Theorem 5, p. 20 (corrected: vacuous moment hypothesis dropped) — the IS ratio estimator F̃_{n₂}(y, ṽ_α) → F_{Y|X}(y | v_α) in probability
-- statement:
--   Let $(X,Y)$ be the delta-gamma pair (17)–(18) with $\gamma_{1d}>0$, whose law has the joint density $f$ of the paper's model; let $\alpha,\beta\in(0,1)$, $v_\alpha=\mathrm{VaR}_\alpha(X)$ and $\mathrm{CoVaR}_{\alpha,\beta}$ satisfy (1)–(2), and suppose Assumptions 1 and 2 hold. Let $n_1,n_2\ge1$ with $n_1\to\infty$ and $n_2\to\infty$, let $\tilde v_\alpha=X_{(\lceil\alpha n_1\rceil)}$ be the first-stage VaR estimator, and let $\tilde F_{n_2}(y,\tilde v_\alpha)$ be the ratio estimator (25)–(26) built from $n_2$ independent second-stage draws. Then for every $y\in\mathcal Y$,
--   $$\tilde F_{n_2}(y,\tilde v_\alpha)\ \to\ F_{Y|X}(y\mid v_\alpha)\qquad\text{in probability.}$$
--
--   The ratio estimator is thus a consistent estimator of the conditional distribution function at the VaR. Inverting it at $\beta$ gives the consistency of $\tilde Y^{\mathrm{IS}}$ (Theorem 6).
--
--   **Formalization Note** $F_{Y|X}(\cdot\mid\cdot)$ is the version `Fc` of (3) of the published base setting (it agrees with $\int_{-\infty}^y f(x,v)\,dv/f_X(x)$ wherever $f_X(x)>0$). Its identification with $\mathrm E[Q(y,v_\alpha)]/\mathrm E[Q(v_\alpha)]$ is not assumed. The sample sizes are sequences $n_1(\nu),n_2(\nu)$ indexed by $\nu$; $\tilde F_{n_2}$ is $0$ on the event that every $\tilde q$ vanishes.
--
--   Differences from the source:
--   - generalization: hypothesis sup_{n1} E[|ṽ_α − g*|^{−1}] < ∞ → dropped; reason: the printed hypothesis is never satisfied in the delta-gamma model (at n₁ = 1, ṽ_α = X_1 and E[|X_1 − g*|^{−1}] = ∞; when g* has a density this holds for every n₁), so Theorem 5 as printed is vacuous; the Lean statement implies the printed one, and its conclusion holds without the hypothesis (DISPROOF.md)
--   - generalization: §4.2.2 (p. 18) orders the factors so that γ_{1d} = max{γ_{11}, …, γ_{1d}} > 0 → only γ_{1d} > 0; reason: no statement uses the ordering; every model with the ordering satisfies γ_{1d} > 0, so the Lean statement specializes to the source's
--   - encoding: X, Y continuous with joint density f; VaR_α(X) = v with F_X(v) = α; CoVaR_{α,β} = c with F_{Y|X}(c | v) = β; the delta-gamma pair (17)–(18) → the published JointDensity D with lawXY M = D.law, D.FX v = α, a version Fc of (3) with Fc c v = β, and Assumption1 D Fc v c 𝒳 𝒴; reason: the standing model of §2 (pp. 4–5) in the base mission's published encoding; v and c are unique under Assumption 1, so data plus defining equations is faithful
--   - encoding: Assumption 2: E[Q(x)] and E[Q(y, x)] are twice differentiable functions of x for all x ∈ ℝ and y ∈ 𝒴 → Assumption2: Q(x) and Q(y, x) (y ∈ 𝒴) integrable over W for every x, and both expectations twice differentiable on ℝ; reason: a twice differentiable real function of x presupposes that the expectation is finite; Q ≥ 0, so finiteness is integrability
--   - encoding: Step 1: n₁ observations of (Z_1, …, Z_d); Step 2: n₂ observations of (Z_1, …, Z_{d−1}), generated independently → IsTwoStageSample: pairs (Z1 i, W2 i) independent across i, each with law N(0, I_d) ⊗ N(0, I_{d−1}); the first n₁ (resp. n₂) terms are used; reason: one coupling of the samples for all n₁, n₂; convergence in probability depends only on the law at each (n₁, n₂), and Lemma 6's w.p.1 limit is along one sequence of first-stage draws, as in the proof (Serfling)
--   - encoding: n₁ → ∞ and n₂ → ∞ as n → ∞, with n₁, n₂ positive integers, n₁ + n₂ = n → sequences n1(ν), n2(ν) ≥ 1 tending to ∞; reason: every admissible (n₁(n), n₂(n)) is such a pair of sequences (ν = n); no rate condition, as on the page
--   - reading: Theorem 5 with a free y → y ∈ 𝒴; reason: Assumption 2, which the proof uses, is stated for y ∈ 𝒴 only, and F_{Y|X}(y | v_α) is pinned down by Assumption 1 only for y ∈ 𝒴 (outside 𝒴 the density may be changed on the null line x = v_α)
--   - encoding: F̃_{n2}(y, ṽ_α) of (25)–(26) → Ftilde, with value 0 when every q̃ vanishes (Lean's 0/0 = 0); reason: the ratio is undefined on that event; its probability tends to 0, so the convention does not affect convergence in probability
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 20, Theorem 5; (25) p. 19, (26) p. 19; Assumption 2 p. 20

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Definitions.Def_CoVaRMC_Batching_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching.Supplement

/-- Theorem 5, p. 20 (corrected: the never-satisfied moment hypothesis is dropped): under
Assumptions 1 and 2, with `n₁, n₂ ≥ 1` and `n₁ → ∞`, `n₂ → ∞`, for `y ∈ 𝒴`,
`F̃_{n₂}(y, ṽ_α) → F_{Y|X}(y | v_α)` in probability. -/
theorem theorem_5 {d' : ℕ} (M : DeltaGamma d') (hγ : 0 < M.γ1d)
    (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β) (hlaw : lawXY M = D.law) (hA2 : Assumption2 M 𝒴)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z1 : ℕ → Ω → (Fin d' → ℝ) × ℝ) (W2 : ℕ → Ω → Fin d' → ℝ) (hS : IsTwoStageSample P Z1 W2)
    (n1 n2 : ℕ → ℕ) (hn1 : ∀ ν, 0 < n1 ν) (hn2 : ∀ ν, 0 < n2 ν)
    (hn1t : Tendsto n1 atTop atTop) (hn2t : Tendsto n2 atTop atTop) :
    ∀ y ∈ 𝒴, TendstoInMeasure P
      (fun ν ω => Ftilde M W2 (n2 ν) y (vTilde M Z1 α (n1 ν) ω) ω) atTop (fun _ => Fc y v) := by sorry

end CoVaRMC.Batching.Supplement
