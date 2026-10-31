-- Prove2me | Theorems.Thm_CompositeSAA_empirical_estimator_slln
-- name    : CompositeSAA.empirical_estimator_slln
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:17.03542+00:00
-- url     : https://prove2.me/theorems/4126d6e7-b422-49f0-a638-64b4b3518262
-- title:
--   Proposition 5 — strong consistency of the empirical composite estimator (corrected: nonempty empirical solution sets)
-- statement:
--   Assume the standing assumptions on problem (3), and let $X_1,X_2,\dots$ be independent random vectors with law $P$. Assume that $f_j(u,\eta_j,\cdot)$ ($j\le k$) and $f_{k+1}(u,\cdot)$ are bounded uniformly in $u\in\mathcal U$, $\eta_j\in I_j$ by $P$-integrable functions $g_j:\mathbb R^m\to\mathbb R$:
--
--   $$
--   \|f_j(u,\eta_j,x)\|\le g_j(x),\qquad\|f_{k+1}(u,x)\|\le g_{k+1}(x)\qquad\text{for all } x\in\mathcal X,
--   $$
--
--   and that, almost surely, for all $N$ large enough the empirical problem has a nonempty solution set $S^{(N)}_E\subseteq\mathcal U$ (Assumption 2 for $Q^j_N=P_N$). Then, almost surely,
--
--   1. $\varrho^{(N)}_E[u,X]\to\varrho[u,X]$ for every $u\in\mathcal U$;
--   2. $\vartheta^{(N)}_E\to\vartheta$;
--   3. $\mathsf d(S^{(N)}_E,S)\to0$;
--   4. if problem (3) has a unique solution $\hat u$, then $\mathsf D(S^{(N)}_E,S)\to0$.
--
--   So every solution of the empirical composite problem, which uses the entire sample at every level, is a strongly consistent estimator of the true solution.
--
--   Differences from the source:
--   - correction: Assumption 2 for $Q^j_N=P_N$ → with "$S^{(N)}_E\ne\emptyset$" added, almost surely; reason: as printed it holds vacuously on an empty solution set and the proposition is false: for $X\sim N(0,1)$, $f_1(u,\eta,x)=u^2/(1+u^2)+ux$, $f_2=0$, $U=\mathbb R$, $\mathcal U=I_1=[-1,1]$, envelopes $g=1+|x|$, the empirical objective $u^2/(1+u^2)+u\bar X_N$ has no minimum whenever $\bar X_N\ne0$, i.e. almost surely.
--   - encoding: the printed "Assumption 1" → Assumption 2 of p.6; reason: label slip in the cross-reference.
--   - generalization: "for every $u\in\mathcal U$, almost surely" → "almost surely, for every $u\in\mathcal U$" (one null set for all $u$); reason: implies the printed order.
--   - generalization: "without loss of generality $\mathcal U$ and $I_j$ are convex" → not assumed; reason: convex sets are an instance.
--   - encoding: i.i.d. sample as mutually independent `X i` each with law $P$, the paper's $X_1,\dots,X_N$ being `X 0, …, X (N-1)`; $\mathbb R^d$, $\mathsf d$, $\mathsf D$, $S$, $\vartheta$ as in Theorem 3; reason: Lean convention, same instances.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, Proposition 5, p.9 (with Assumption 2, p.6)

import Mathlib
import Definitions.Def_CompositeSAA_CompositeModel
import Definitions.Def_CompositeSAA_empiricalEstimator
import Definitions.Def_CompositeSAA_riskFunctional
import Definitions.Def_CompositeSAA_optimalValue
import Definitions.Def_CompositeSAA_solutionSet
import Definitions.Def_CompositeSAA_excess
import Definitions.Def_CompositeSAA_StandingAssumptions

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, Proposition 5, p.9 (corrected): strong consistency
of the empirical composite estimator.

Under the standing assumptions, let `X_1, X_2, …` be i.i.d. with law `P`. Assume that
`f_j(u, η_j, ·)` and `f_{k+1}(u, ·)` are bounded uniformly in `u ∈ 𝒰`, `η_j ∈ I_j` by
`P`-integrable functions `g_j`: `‖f_j(u, η_j, x)‖ ≤ g_j(x)` and `‖f_{k+1}(u, x)‖ ≤ g_{k+1}(x)` for
all `x ∈ 𝒳`, and that, almost surely, for `N` large the empirical solution set `S^{(N)}_E` is
nonempty and contained in `𝒰` (Assumption 2 for `Q^j_N = P_N`). Then, almost surely,
`ϱ^{(N)}_E[u] → ϱ[u]` for every `u ∈ 𝒰`, `ϑ^{(N)}_E → ϑ`, `d(S^{(N)}_E, S) → 0`, and if `S = {û}`
then `D(S^{(N)}_E, S) → 0`.

**Formalization Note**
1. The sample is `X : ℕ → Ω → ℝ^{mX}`, mutually independent, each with law `P`; the paper's
   `X_1, …, X_N` are `X 0, …, X (N − 1)`.
2. Correction: Assumption 2 includes `S^{(N)}_E ≠ ∅`; the printed "Assumption 1" is
   Assumption 2.
3. One null set serves all `u ∈ 𝒰` (`∀ᵐ ω, ∀ u ∈ 𝒰`), which implies the printed "for every
   `u ∈ 𝒰`, almost surely". -/
theorem empirical_estimator_slln {n mX k : ℕ} (D : CompositeModel n mX k)
    (P : Measure (EuclideanSpace ℝ (Fin mX))) (𝒳 : Set (EuclideanSpace ℝ (Fin mX)))
    (U 𝒰 : Set (EuclideanSpace ℝ (Fin n)))
    (I : (j : ℕ) → Set (EuclideanSpace ℝ (Fin (D.m j))))
    (hstd : StandingAssumptions D P 𝒳 U 𝒰 I)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin mX)) (hindep : iIndepFun X Pr)
    (hlaw : ∀ i, HasLaw (X i) P Pr)
    (g : ℕ → EuclideanSpace ℝ (Fin mX) → ℝ)
    (hg : ∀ j, 1 ≤ j → j ≤ k + 1 → Integrable (g j) P)
    (henv : ∀ j, 1 ≤ j → j ≤ k → ∀ u ∈ 𝒰, ∀ η ∈ I j, ∀ x ∈ 𝒳, ‖D.f j u η x‖ ≤ g j x)
    (henvLast : ∀ u ∈ 𝒰, ∀ x ∈ 𝒳, ‖D.fLast u x‖ ≤ g (k + 1) x)
    (hA2 : ∀ᵐ ω ∂Pr, ∀ᶠ N in atTop,
      (solutionSet (empiricalEstimator D N (fun i => X i ω)) U).Nonempty ∧
        solutionSet (empiricalEstimator D N (fun i => X i ω)) U ⊆ 𝒰) :
    ∀ᵐ ω ∂Pr,
      (∀ u ∈ 𝒰, Tendsto (fun N => empiricalEstimator D N (fun i => X i ω) u) atTop
          (𝓝 (riskFunctional D P u))) ∧
        Tendsto (fun N => optimalValue (empiricalEstimator D N (fun i => X i ω)) U) atTop
          (𝓝 (optimalValue (riskFunctional D P) U)) ∧
        Tendsto (fun N => excess (solutionSet (empiricalEstimator D N (fun i => X i ω)) U)
          (solutionSet (riskFunctional D P) U)) atTop (𝓝 0) ∧
        ∀ û, solutionSet (riskFunctional D P) U = {û} →
          Tendsto (fun N => Metric.hausdorffEDist
            (solutionSet (empiricalEstimator D N (fun i => X i ω)) U)
            (solutionSet (riskFunctional D P) U)) atTop (𝓝 0) := by sorry

end CompositeSAA
