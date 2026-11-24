-- Prove2me | Theorems.Thm_CoVaRMC_Batching_Supplement_theorem_6
-- name    : CoVaRMC.Batching.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:16:32.589544+00:00
-- url     : https://prove2.me/theorems/398a65fe-dde1-48b9-ab2e-83c2b6f98d73
-- title:
--   Theorem 6, p. 21 (corrected: vacuous moment hypothesis dropped) — the IS-inspired estimator Ỹ^IS → CoVaR_{α,β} in probability
-- statement:
--   In the setting of Theorem 5 (delta-gamma pair with $\gamma_{1d}>0$ and joint density $f$, $\alpha,\beta\in(0,1)$, Assumptions 1 and 2, $n_1,n_2\ge1$ with $n_1\to\infty$ and $n_2\to\infty$), let
--   $$\tilde Y^{\mathrm{IS}}=\inf\{y\in\mathbb R:\tilde F_{n_2}(y,\tilde v_\alpha)\ge\beta\}$$
--   be the IS-inspired estimator of §4.2.2. Then
--   $$\tilde Y^{\mathrm{IS}}\ \to\ \mathrm{CoVaR}_{\alpha,\beta}\qquad\text{in probability.}$$
--
--   This is the consistency of the second CoVaR estimator of the paper, the counterpart for the delta-gamma model of the batching estimator's consistency.
--
--   **Formalization Note** $\mathrm{CoVaR}_{\alpha,\beta}$ is the real `c` with `Fc c v = β` of the published base setting. $\tilde Y^{\mathrm{IS}}$ is defined by the infimum, the paper's own identity on p. 20; it is $\inf\emptyset=0$ on the event that every $\tilde q$ vanishes, whose probability tends to $0$.
--
--   Differences from the source:
--   - generalization: hypothesis sup_{n1} E[|ṽ_α − g*|^{−1}] < ∞ → dropped; reason: the printed hypothesis is never satisfied in the delta-gamma model (at n₁ = 1, ṽ_α = X_1 and E[|X_1 − g*|^{−1}] = ∞; when g* has a density this holds for every n₁), so Theorem 6 as printed is vacuous; the Lean statement implies the printed one, and its conclusion holds without the hypothesis (DISPROOF.md)
--   - generalization: §4.2.2 (p. 18) orders the factors so that γ_{1d} = max{γ_{11}, …, γ_{1d}} > 0 → only γ_{1d} > 0; reason: no statement uses the ordering; every model with the ordering satisfies γ_{1d} > 0, so the Lean statement specializes to the source's
--   - encoding: X, Y continuous with joint density f; VaR_α(X) = v with F_X(v) = α; CoVaR_{α,β} = c with F_{Y|X}(c | v) = β; the delta-gamma pair (17)–(18) → the published JointDensity D with lawXY M = D.law, D.FX v = α, a version Fc of (3) with Fc c v = β, and Assumption1 D Fc v c 𝒳 𝒴; reason: the standing model of §2 (pp. 4–5) in the base mission's published encoding; v and c are unique under Assumption 1, so data plus defining equations is faithful
--   - encoding: Assumption 2: E[Q(x)] and E[Q(y, x)] are twice differentiable functions of x for all x ∈ ℝ and y ∈ 𝒴 → Assumption2: Q(x) and Q(y, x) (y ∈ 𝒴) integrable over W for every x, and both expectations twice differentiable on ℝ; reason: a twice differentiable real function of x presupposes that the expectation is finite; Q ≥ 0, so finiteness is integrability
--   - encoding: Step 1: n₁ observations of (Z_1, …, Z_d); Step 2: n₂ observations of (Z_1, …, Z_{d−1}), generated independently → IsTwoStageSample: pairs (Z1 i, W2 i) independent across i, each with law N(0, I_d) ⊗ N(0, I_{d−1}); the first n₁ (resp. n₂) terms are used; reason: one coupling of the samples for all n₁, n₂; convergence in probability depends only on the law at each (n₁, n₂), and Lemma 6's w.p.1 limit is along one sequence of first-stage draws, as in the proof (Serfling)
--   - encoding: n₁ → ∞ and n₂ → ∞ as n → ∞, with n₁, n₂ positive integers, n₁ + n₂ = n → sequences n1(ν), n2(ν) ≥ 1 tending to ∞; reason: every admissible (n₁(n), n₂(n)) is such a pair of sequences (ν = n); no rate condition, as on the page
--   - encoding: Ỹ^IS = Ỹ_(m) from the weighted sort of Step 3 (p. 19) → Ỹ^IS = sInf {y | β ≤ F̃_{n2}(y, ṽ_α)}; reason: the paper states this identity on p. 20 ('it is easy to recognize that Ỹ^IS satisfies Ỹ^IS = inf{y ∈ ℝ : F̃_{n2}(y, ṽ_α) ≥ β}'); the weighted sort differs only when a partial weight sum equals β exactly, and both choices give the same limit; sInf ∅ = 0 on the event that every q̃ vanishes, whose probability tends to 0
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 21, Theorem 6; the identity Ỹ^IS = inf{y ∈ ℝ : F̃_{n2}(y, ṽ_α) ≥ β}, p. 20

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Definitions.Def_CoVaRMC_Batching_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching.Supplement

/-- Theorem 6, p. 21 (corrected: the never-satisfied moment hypothesis is dropped): under
Assumptions 1 and 2, with `n₁, n₂ ≥ 1` and `n₁ → ∞`, `n₂ → ∞`,
`Ỹ^IS → CoVaR_{α,β}` in probability. -/
theorem theorem_6 {d' : ℕ} (M : DeltaGamma d') (hγ : 0 < M.γ1d)
    (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β) (hlaw : lawXY M = D.law) (hA2 : Assumption2 M 𝒴)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z1 : ℕ → Ω → (Fin d' → ℝ) × ℝ) (W2 : ℕ → Ω → Fin d' → ℝ) (hS : IsTwoStageSample P Z1 W2)
    (n1 n2 : ℕ → ℕ) (hn1 : ∀ ν, 0 < n1 ν) (hn2 : ∀ ν, 0 < n2 ν)
    (hn1t : Tendsto n1 atTop atTop) (hn2t : Tendsto n2 atTop atTop) :
    TendstoInMeasure P (fun ν ω => YIS M Z1 W2 α β (n1 ν) (n2 ν) ω) atTop (fun _ => c) := by sorry

end CoVaRMC.Batching.Supplement
