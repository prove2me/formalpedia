-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_theorem_4_12
-- name    : ExactLearningSeparation678.Randomized.Supplement.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:06.545041+00:00
-- url     : https://prove2.me/theorems/eb69228b-2da8-4bfc-9452-1a2d7f834c1c
-- title:
--   Theorem 4.12 — $R(C)=O(\mathrm{fETD}(C)\log|C|/\log(1+\mathrm{fETD}(C)))$
-- statement:
--   There is an absolute constant $K>0$ such that for every concept class $C\subseteq\{0,1\}^N$,
--   $$R(C)\le K\,\frac{\mathrm{fETD}(C)\,\log|C|}{\log\big(1+\mathrm{fETD}(C)\big)},$$
--   where $R(C)$ is the randomized query complexity of exactly learning $C$ (success probability at least $2/3$ on every target, worst-case number of queries) and $\mathrm{fETD}(C)$ is the fractional extended teaching dimension.
--
--   It is a randomized, fractional analogue of the deterministic $\mathrm{ETD}$ upper bound of Hegedűs and Moshkov.
--
--   **Formalization Note** The constant precedes the coordinate set and the class. Logarithms are natural. For $|C|\le1$, $\mathrm{fETD}(C)=0$ and the right side is $0/0$, which real division reads as $0$; then $R(C)=0$.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: bounded-error quantum and randomized query complexities Q(C), R(C) → the published quantumExactComplexity (QueryAlg, XOR oracle, any finite workspace) and classicalExactComplexity (randomized decision trees, worst-case query bound), success ≥ 2/3 on every target; reason: the mission’s published models of the source’s Q and R
--   - encoding: R(C) = O(fETD(C) log|C| / log(1+fETD(C))) for every C → one K > 0 quantified before ι and C, bounding the worst-case randomized query complexity; reason: the source’s O is uniform over all classes; the bound is on R itself, not on an expected depth
--   - encoding: logarithms of unspecified base → natural logarithm Real.log; reason: a change of base is absorbed into the absolute constant
--   - encoding: fETD(C,h) minimizes over c* ∈ C and all real nonnegative coordinate weights, then fETD(C) maximizes over every ambient h → fetdAt is the real infimum of the same total-weight objective over feasible pairs (c*, w); fetd is the supremum over all ambient Boolean functions; reason: for C nonempty feasible weights exist and can be clipped to [0,1] without violating any constraint or increasing cost; finitely many c* and compact weight cubes give attainment, and the outer index is finite and nonempty
--   - reading: γ and fγ have no feasible optimization point when |C| ≤ 1; fETD has none only when C is empty; the source assigns no value in these cases → empty real infima are 0 and real division by 0 is 0; fETD of a singleton is already 0 using feasible zero weights; reason: this supplies values only for undefined degenerate extrema; every trivial-class clause is true and every source-defined nontrivial instance is retained
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 4.12, p.34 (proof pp.34–36); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Theorem 4.12, p.34: `R(C) = O(fETD(C) log |C| / log(1 + fETD(C)))` uniformly: one absolute
`K > 0`, fixed before `N` and `C`, bounds the worst-case randomized exact-learning complexity
for every concept class. Natural logarithms; real division by `0` is `0`. -/
theorem theorem_4_12 : ∃ K : ℝ, 0 < K ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)),
      (classicalExactComplexity C : ℝ) ≤
        K * (fetd C * Real.log (C.card : ℝ) / Real.log (1 + fetd C)) := by sorry

end ExactLearningSeparation678.Randomized.Supplement
