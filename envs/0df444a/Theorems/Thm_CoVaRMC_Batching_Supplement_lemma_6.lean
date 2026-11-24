-- Prove2me | Theorems.Thm_CoVaRMC_Batching_Supplement_lemma_6
-- name    : CoVaRMC.Batching.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:14:36.572975+00:00
-- url     : https://prove2.me/theorems/c4d27eab-2b6c-4f58-b5d9-dd326852744a
-- title:
--   Lemma 6, p. 20 — errors II and IV: E[Q(y, ṽ_α)|ṽ_α] → E[Q(y, v_α)] and E[Q(ṽ_α)|ṽ_α] → E[Q(v_α)] w.p.1 as n₁ → ∞
-- statement:
--   Let $(X,Y)$ be the delta-gamma pair (17)–(18) with $\gamma_{1d}>0$, whose law has the joint density $f$ of the paper's model, and let $\alpha,\beta\in(0,1)$, $v_\alpha=\mathrm{VaR}_\alpha(X)$ and $\mathrm{CoVaR}_{\alpha,\beta}$ satisfy (1)–(2). Suppose Assumption 1 holds (with neighbourhoods $\mathcal X\ni v_\alpha$, $\mathcal Y\ni\mathrm{CoVaR}_{\alpha,\beta}$) and Assumption 2 holds. Let $\tilde v_\alpha=X_{(\lceil\alpha n_1\rceil)}$ be the first-stage VaR estimator from $n_1$ i.i.d. draws, and let the second stage be independent of it. Then for every $y\in\mathcal Y$, with probability one,
--   $$\mathrm E[Q(y,\tilde v_\alpha)\mid\tilde v_\alpha]\to\mathrm E[Q(y,v_\alpha)]\quad\text{and}\quad\mathrm E[Q(\tilde v_\alpha)\mid\tilde v_\alpha]\to\mathrm E[Q(v_\alpha)]\qquad(n_1\to\infty).$$
--
--   These are the errors II and IV of the decomposition of the numerator and denominator of $\tilde F_{n_2}(y,\tilde v_\alpha)$ on p. 20. Together with Lemma 7 they give the consistency of $\tilde F_{n_2}$ (Theorem 5).
--
--   **Formalization Note** The conditional expectations given $\tilde v_\alpha$ are the deterministic functions $x\mapsto\mathrm E_W[Q(y,x)]$ and $x\mapsto\mathrm E_W[Q(x)]$ evaluated at $\tilde v_\alpha$ (`EQy`, `EQ`), which is legitimate because the second stage is independent of the first. The model, VaR, CoVaR and Assumption 1 are those of the published `CoVaRMC.Batching.Setting`, linked to the delta-gamma pair by `lawXY M = D.law`. The w.p.1 statement is along one sequence of first-stage draws.
--
--   Differences from the source:
--   - encoding: X, Y continuous with joint density f; VaR_α(X) = v with F_X(v) = α; CoVaR_{α,β} = c with F_{Y|X}(c | v) = β; the delta-gamma pair (17)–(18) → the published JointDensity D with lawXY M = D.law, D.FX v = α, a version Fc of (3) with Fc c v = β, and Assumption1 D Fc v c 𝒳 𝒴; reason: the standing model of §2 (pp. 4–5) in the base mission's published encoding; v and c are unique under Assumption 1, so data plus defining equations is faithful
--   - encoding: Assumption 2: E[Q(x)] and E[Q(y, x)] are twice differentiable functions of x for all x ∈ ℝ and y ∈ 𝒴 → Assumption2: Q(x) and Q(y, x) (y ∈ 𝒴) integrable over W for every x, and both expectations twice differentiable on ℝ; reason: a twice differentiable real function of x presupposes that the expectation is finite; Q ≥ 0, so finiteness is integrability
--   - encoding: conditional expectations E[Q(y, ṽ_α) | ṽ_α] and E[Q(ṽ_α) | ṽ_α] → x ↦ E_W[Q(y, x)] and x ↦ E_W[Q(x)] evaluated at x = ṽ_α; reason: the second-stage draws are independent of ṽ_α, so these are versions of the conditional expectations
--   - encoding: Step 1: n₁ observations of (Z_1, …, Z_d); Step 2: n₂ observations of (Z_1, …, Z_{d−1}), generated independently → IsTwoStageSample: pairs (Z1 i, W2 i) independent across i, each with law N(0, I_d) ⊗ N(0, I_{d−1}); the first n₁ (resp. n₂) terms are used; reason: one coupling of the samples for all n₁, n₂; convergence in probability depends only on the law at each (n₁, n₂), and Lemma 6's w.p.1 limit is along one sequence of first-stage draws, as in the proof (Serfling)
--   - reading: Lemma 6 with a free y → y ∈ 𝒴; reason: Assumption 2, which the proof uses, is stated for y ∈ 𝒴 only, and F_{Y|X}(y | v_α) is pinned down by Assumption 1 only for y ∈ 𝒴 (outside 𝒴 the density may be changed on the null line x = v_α)
--   - generalization: §4.2.2 (p. 18) orders the factors so that γ_{1d} = max{γ_{11}, …, γ_{1d}} > 0 → only γ_{1d} > 0; reason: no statement uses the ordering; every model with the ordering satisfies γ_{1d} > 0, so the Lean statement specializes to the source's
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 20, Lemma 6; Assumption 2 (p. 20); proof Appendix C, p. 35

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Definitions.Def_CoVaRMC_Batching_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching.Supplement

/-- Lemma 6, p. 20: under Assumptions 1 and 2, for `y ∈ 𝒴`,
`E[Q(y, ṽ_α) | ṽ_α] → E[Q(y, v_α)]` and `E[Q(ṽ_α) | ṽ_α] → E[Q(v_α)]` w.p.1 as `n₁ → ∞`; by
independence of the two stages the conditional expectations are `x ↦ E[Q(y, x)]` and
`x ↦ E[Q(x)]` evaluated at `x = ṽ_α`. -/
theorem lemma_6 {d' : ℕ} (M : DeltaGamma d') (hγ : 0 < M.γ1d)
    (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β) (hlaw : lawXY M = D.law) (hA2 : Assumption2 M 𝒴)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z1 : ℕ → Ω → (Fin d' → ℝ) × ℝ) (W2 : ℕ → Ω → Fin d' → ℝ) (hS : IsTwoStageSample P Z1 W2) :
    ∀ y ∈ 𝒴, ∀ᵐ ω ∂P,
      Tendsto (fun n1 => EQy M y (vTilde M Z1 α n1 ω)) atTop (𝓝 (EQy M y v)) ∧
      Tendsto (fun n1 => EQ M (vTilde M Z1 α n1 ω)) atTop (𝓝 (EQ M v)) := by sorry

end CoVaRMC.Batching.Supplement
