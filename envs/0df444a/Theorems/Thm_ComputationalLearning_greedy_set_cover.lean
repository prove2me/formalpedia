-- Prove2me | Theorems.Thm_ComputationalLearning_greedy_set_cover
-- name    : ComputationalLearning.greedy_set_cover
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:04:08.829495+00:00
-- url     : https://prove2.me/theorems/6d7d174c-bdda-4c24-b396-2d10df94c92c
-- title:
--   The greedy set cover bound (§2.3): after i steps at most (1 − 1/opt)^i |U| elements are uncovered, and opt ln|U| sets cover U
-- statement:
--   **The greedy set cover bound** (p. 39). Let $U_i \subseteq U$ denote the set of elements still not covered after $i$ steps of the greedy heuristic. Then $|U_{i+1}| \le |U_i|(1 - 1/\mathrm{opt}(\mathcal{S}))$, so by induction $|U_i| \le (1 - 1/\mathrm{opt}(\mathcal{S}))^i |U|$, and choosing $i \ge \mathrm{opt}(\mathcal{S}) \log |U|$ suffices to drive this bound below $1$: all the elements of $U$ are covered after the algorithm has chosen $\mathrm{opt}(\mathcal{S})\log|U|$ sets.
--
--   Formally: for a collection $\mathcal{S}$ covering the finite universe $U$ and every greedy run $t$: for all $i$, $|\mathrm{uncovered}(t, i)| \le (1 - 1/\mathrm{opt}(\mathcal{S}))^i |U|$; and for all $i \ge 1$ with $\mathrm{opt}(\mathcal{S}) \ln|U| \le i$, $\mathrm{uncovered}(t, i) = \emptyset$ (the strict inequality $1 - x < e^{-x}$ for $x > 0$ makes the bound strictly less than $1$).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §2.3 pp. 38-39, the greedy heuristic and its analysis (Chvátal 1979)

import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory

namespace ComputationalLearning

/-- **The greedy set cover bound** (§2.3, p. 39; Chvátal 1979). Let `𝒮` be a collection of subsets
of the finite universe `U` that covers `U`, and let `t` be a run of the greedy heuristic. Then
after `i` steps at most `(1 − 1/opt(𝒮))^i |U|` elements are uncovered, and all the elements of
`U` are covered after the heuristic has chosen `opt(𝒮) ln|U|` sets (at least one). -/
theorem greedy_set_cover {U : Type*} [DecidableEq U] [Fintype U] (𝒮 : Finset (Finset U))
    (hcov : IsCover 𝒮 𝒮) (t : ℕ → Finset U) (ht : IsGreedySequence 𝒮 t) :
    (∀ i : ℕ, ((uncovered t i).card : ℝ) ≤
      (1 - 1 / (optCover 𝒮 : ℝ)) ^ i * (Fintype.card U : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → (optCover 𝒮 : ℝ) * Real.log (Fintype.card U) ≤ i →
      uncovered t i = ∅) := by sorry

end ComputationalLearning
