-- Prove2me | Theorems.Thm_CoVaRMC_Batching_Supplement_lemma_7
-- name    : CoVaRMC.Batching.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:15:11.784189+00:00
-- url     : https://prove2.me/theorems/6a802097-3dc3-492f-a227-4e29974cd204
-- title:
--   Lemma 7, p. 20 (corrected: vacuous moment hypothesis dropped) — errors I and III → 0 in probability as n₂ → ∞, uniformly in n₁
-- statement:
--   In the setting of Lemma 6 (delta-gamma pair with $\gamma_{1d}>0$ and joint density $f$, $\alpha,\beta\in(0,1)$, Assumptions 1 and 2), let $Q_k(y,x)$ and $Q_k(x)$, $k=1,\dots,n_2$, be computed from the independent second-stage draws $W_1,\dots,W_{n_2}$. Then for every $y\in\mathbb R$,
--   $$\frac1{n_2}\sum_{k=1}^{n_2}Q_k(y,\tilde v_\alpha)-\mathrm E[Q(y,\tilde v_\alpha)\mid\tilde v_\alpha]\to0\quad\text{and}\quad\frac1{n_2}\sum_{k=1}^{n_2}Q_k(\tilde v_\alpha)-\mathrm E[Q(\tilde v_\alpha)\mid\tilde v_\alpha]\to0$$
--   in probability as $n_2\to\infty$, uniformly in the first-stage size $n_1\ge1$.
--
--   These are the errors I and III of the decomposition on p. 20: the second-stage sampling errors of the numerator and denominator of $\tilde F_{n_2}(y,\tilde v_\alpha)$, measured against their conditional means.
--
--   **Formalization Note** Uniformity in $n_1$ is stated as convergence along every pair of sequences $n_1(\nu)\ge1$ (arbitrary) and $n_2(\nu)\to\infty$. Convergence in probability is `TendstoInMeasure`. The conditional means are `EQy`, `EQ` at $\tilde v_\alpha$, as in Lemma 6.
--
--   Differences from the source:
--   - generalization: hypothesis sup_{n1} E[|ṽ_α − g*|^{−1}] < ∞ → dropped; reason: the printed hypothesis is never satisfied in the delta-gamma model (at n₁ = 1, ṽ_α = X_1 and E[|X_1 − g*|^{−1}] = ∞; when g* has a density this holds for every n₁), so Lemma 7 as printed is vacuous; the Lean statement implies the printed one, and its conclusion holds without the hypothesis (DISPROOF.md)
--   - generalization: §4.2.2 (p. 18) orders the factors so that γ_{1d} = max{γ_{11}, …, γ_{1d}} > 0 → only γ_{1d} > 0; reason: no statement uses the ordering; every model with the ordering satisfies γ_{1d} > 0, so the Lean statement specializes to the source's
--   - encoding: X, Y continuous with joint density f; VaR_α(X) = v with F_X(v) = α; CoVaR_{α,β} = c with F_{Y|X}(c | v) = β; the delta-gamma pair (17)–(18) → the published JointDensity D with lawXY M = D.law, D.FX v = α, a version Fc of (3) with Fc c v = β, and Assumption1 D Fc v c 𝒳 𝒴; reason: the standing model of §2 (pp. 4–5) in the base mission's published encoding; v and c are unique under Assumption 1, so data plus defining equations is faithful
--   - encoding: Assumption 2: E[Q(x)] and E[Q(y, x)] are twice differentiable functions of x for all x ∈ ℝ and y ∈ 𝒴 → Assumption2: Q(x) and Q(y, x) (y ∈ 𝒴) integrable over W for every x, and both expectations twice differentiable on ℝ; reason: a twice differentiable real function of x presupposes that the expectation is finite; Q ≥ 0, so finiteness is integrability
--   - encoding: conditional expectations E[Q(y, ṽ_α) | ṽ_α] and E[Q(ṽ_α) | ṽ_α] → x ↦ E_W[Q(y, x)] and x ↦ E_W[Q(x)] evaluated at x = ṽ_α; reason: the second-stage draws are independent of ṽ_α, so these are versions of the conditional expectations
--   - encoding: Step 1: n₁ observations of (Z_1, …, Z_d); Step 2: n₂ observations of (Z_1, …, Z_{d−1}), generated independently → IsTwoStageSample: pairs (Z1 i, W2 i) independent across i, each with law N(0, I_d) ⊗ N(0, I_{d−1}); the first n₁ (resp. n₂) terms are used; reason: one coupling of the samples for all n₁, n₂; convergence in probability depends only on the law at each (n₁, n₂), and Lemma 6's w.p.1 limit is along one sequence of first-stage draws, as in the proof (Serfling)
--   - encoding: convergence as n₂ → ∞ under sup over n₁ → TendstoInMeasure along every n1(ν) ≥ 1 and n2(ν) → ∞; reason: uniform convergence in n₁ is equivalent to convergence along every such pair of sequences
--   - generalization: y free on the page, where Assumption 2 (and Lemma 6, read with y ∈ 𝒴) concerns y ∈ 𝒴 → every y ∈ ℝ; reason: Q(y, x) ≤ Q(x), so the integrability and uniform integrability that the conclusion needs come from Q(x) alone; the statement specializes to y ∈ 𝒴
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 20, Lemma 7; proof Appendix D, pp. 35–36

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Definitions.Def_CoVaRMC_Batching_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching.Supplement

/-- Lemma 7, p. 20 (corrected: the never-satisfied moment hypothesis is dropped): under Assumptions 1
and 2, `(1/n₂) ∑_{k=1}^{n₂} Q_k(y, ṽ_α) - E[Q(y, ṽ_α) | ṽ_α] → 0` and
`(1/n₂) ∑_{k=1}^{n₂} Q_k(ṽ_α) - E[Q(ṽ_α) | ṽ_α] → 0` in probability as `n₂ → ∞`, uniformly in
`n₁ ≥ 1` (along every `n₁(ν) ≥ 1` and `n₂(ν) → ∞`). -/
theorem lemma_7 {d' : ℕ} (M : DeltaGamma d') (hγ : 0 < M.γ1d)
    (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β) (hlaw : lawXY M = D.law) (hA2 : Assumption2 M 𝒴)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z1 : ℕ → Ω → (Fin d' → ℝ) × ℝ) (W2 : ℕ → Ω → Fin d' → ℝ) (hS : IsTwoStageSample P Z1 W2)
    (n1 n2 : ℕ → ℕ) (hn1 : ∀ ν, 0 < n1 ν) (hn2 : Tendsto n2 atTop atTop) (y : ℝ) :
    TendstoInMeasure P
      (fun ν ω => (n2 ν : ℝ)⁻¹ * ∑ k ∈ Finset.range (n2 ν), M.Qy y (vTilde M Z1 α (n1 ν) ω) (W2 k ω)
        - EQy M y (vTilde M Z1 α (n1 ν) ω)) atTop (fun _ => 0) ∧
    TendstoInMeasure P
      (fun ν ω => (n2 ν : ℝ)⁻¹ * ∑ k ∈ Finset.range (n2 ν), M.Qx (vTilde M Z1 α (n1 ν) ω) (W2 k ω)
        - EQ M (vTilde M Z1 α (n1 ν) ω)) atTop (fun _ => 0) := by sorry

end CoVaRMC.Batching.Supplement
