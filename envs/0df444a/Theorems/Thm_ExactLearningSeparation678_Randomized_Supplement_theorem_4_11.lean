-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_theorem_4_11
-- name    : ExactLearningSeparation678.Randomized.Supplement.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:30:29.187661+00:00
-- url     : https://prove2.me/theorems/e0ace822-b782-441c-8593-bcfb76749a5f
-- title:
--   Theorem 4.11 — $Q(C)=\Omega(\sqrt{1/f\gamma(C)})$
-- statement:
--   There is an absolute constant $c>0$ such that for every concept class $C\subseteq\{0,1\}^N$,
--   $$Q(C)\ge c\,\sqrt{\frac1{f\gamma(C)}},$$
--   where $Q(C)$ is the bounded-error quantum query complexity of exactly learning $C$ with membership queries and $f\gamma(C)$ is the fractional splitting parameter.
--
--   It strengthens the splitting-parameter quantum lower bound by replacing $\gamma$ with the possibly smaller $f\gamma$.
--
--   **Formalization Note** The constant precedes the coordinate set and the class. For $|C|\le1$ the right side is $0$.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: bounded-error quantum and randomized query complexities Q(C), R(C) → the published quantumExactComplexity (QueryAlg, XOR oracle, any finite workspace) and classicalExactComplexity (randomized decision trees, worst-case query bound), success ≥ 2/3 on every target; reason: the mission’s published models of the source’s Q and R
--   - encoding: Q(C) = Ω(√(1/fγ(C))) for every C → one c > 0 quantified before ι and C; reason: the source’s Ω is uniform over all classes
--   - encoding: fγ(C) is the minimum over all real distributions on C with each atom at most 1/2 → real masses on the members of C, with fGamma the infimum of the finite-coordinate splitting objective over the capped probability simplex; reason: for |C| ≥ 2 the simplex is nonempty and compact and the objective is continuous, so its infimum is an attained minimum
--   - reading: γ and fγ have no feasible optimization point when |C| ≤ 1; fETD has none only when C is empty; the source assigns no value in these cases → empty real infima are 0 and real division by 0 is 0; fETD of a singleton is already 0 using feasible zero weights; reason: this supplies values only for undefined degenerate extrema; every trivial-class clause is true and every source-defined nontrivial instance is retained
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 4.11, p.33 (proof pp.33–34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Theorem 4.11, p.33: `Q(C) = Ω(√(1/fγ(C)))` uniformly: one absolute `c > 0`, fixed before
`N` and `C`, with `c √(1/fγ(C)) ≤ Q(C)` for every concept class. -/
theorem theorem_4_11 : ∃ c : ℝ, 0 < c ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)),
      c * Real.sqrt (1 / fGamma C) ≤ (quantumExactComplexity C : ℝ) := by sorry

end ExactLearningSeparation678.Randomized.Supplement
