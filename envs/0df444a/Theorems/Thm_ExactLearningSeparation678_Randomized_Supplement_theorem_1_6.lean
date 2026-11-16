-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_theorem_1_6
-- name    : ExactLearningSeparation678.Randomized.Supplement.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:33.700222+00:00
-- url     : https://prove2.me/theorems/6c1858db-eb84-4825-b0cd-46460f6bc086
-- title:
--   Theorem 1.6 (companion theorem) — fractional teaching bounds on $Q(C)$ and $R(C)$
-- statement:
--   There are absolute constants $c,K>0$ such that for every concept class $C\subseteq\{0,1\}^N$,
--   $$Q(C)\ge c\sqrt{\mathrm{fETD}(C)},\qquad R(C)\le K\,\frac{\mathrm{fETD}(C)}{\log(\mathrm{fETD}(C)+1)}\,\log|C|,$$
--   and, equivalently,
--   $$Q(C)\ge c\sqrt{1/f\gamma(C)},\qquad R(C)\le K\,\frac{1}{f\gamma(C)\log(1/f\gamma(C)+1)}\,\log|C|.$$
--   Here $Q(C)$ and $R(C)$ are the bounded-error quantum and randomized membership-query complexities of exactly learning $C$, $\mathrm{fETD}$ is the fractional extended teaching dimension and $f\gamma$ the fractional splitting parameter.
--
--   A single fractional parameter thus gives a square-root quantum lower bound and a randomized upper bound, refining both the splitting-parameter lower bound and the extended-teaching-dimension upper bound.
--
--   **Formalization Note** All four bounds are stated. The constants precede the coordinate set and the class. Logarithms are natural; real division by $0$ is $0$, and for $|C|\le1$ the parameters are read as $0$, so every right side is $0$ there, matching $Q(C)=R(C)=0$.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: bounded-error quantum and randomized query complexities Q(C), R(C) → the published quantumExactComplexity (QueryAlg, XOR oracle, any finite workspace) and classicalExactComplexity (randomized decision trees, worst-case query bound), success ≥ 2/3 on every target; reason: the mission’s published models of the source’s Q and R
--   - encoding: Q = Ω(·) and R = O(·) for every C → one c > 0 and one K > 0 quantified before ι and C, for all four displays; reason: the source’s constants are absolute; taking the minimum (maximum) of separate constants gives common ones
--   - encoding: logarithms of unspecified base → natural logarithm Real.log; reason: a change of base is absorbed into the absolute constant
--   - encoding: fγ(C) is the minimum over all real distributions on C with each atom at most 1/2 → real masses on the members of C, with fGamma the infimum of the finite-coordinate splitting objective over the capped probability simplex; reason: for |C| ≥ 2 the simplex is nonempty and compact and the objective is continuous, so its infimum is an attained minimum
--   - encoding: fETD(C,h) minimizes over c* ∈ C and all real nonnegative coordinate weights, then fETD(C) maximizes over every ambient h → fetdAt is the real infimum of the same total-weight objective over feasible pairs (c*, w); fetd is the supremum over all ambient Boolean functions; reason: for C nonempty feasible weights exist and can be clipped to [0,1] without violating any constraint or increasing cost; finitely many c* and compact weight cubes give attainment, and the outer index is finite and nonempty
--   - reading: γ and fγ have no feasible optimization point when |C| ≤ 1; fETD has none only when C is empty; the source assigns no value in these cases → empty real infima are 0 and real division by 0 is 0; fETD of a singleton is already 0 using feasible zero weights; reason: this supplies values only for undefined degenerate extrema; every trivial-class clause is true and every source-defined nontrivial instance is retained
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 1.6, p.12; derivation p.36; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Theorem 1.6, p.12: for every concept class `C ⊆ {0,1}^N`, with absolute constants `c, K > 0`
fixed before `N` and `C`: `Q(C) ≥ c √fETD(C)`, `R(C) ≤ K · fETD(C)/log(fETD(C)+1) · log |C|`,
and the equivalent forms `Q(C) ≥ c √(1/fγ(C))`,
`R(C) ≤ K · 1/(fγ(C) log(1/fγ(C)+1)) · log |C|`. Natural logarithms; real division by `0` is
`0`, which with the zero reading of `fγ`, `fETD` at `|C| ≤ 1` keeps trivial classes. -/
theorem theorem_1_6 : ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)),
      c * Real.sqrt (fetd C) ≤ (quantumExactComplexity C : ℝ) ∧
      (classicalExactComplexity C : ℝ) ≤
        K * (fetd C / Real.log (fetd C + 1)) * Real.log (C.card : ℝ) ∧
      c * Real.sqrt (1 / fGamma C) ≤ (quantumExactComplexity C : ℝ) ∧
      (classicalExactComplexity C : ℝ) ≤
        K * (1 / (fGamma C * Real.log (1 / fGamma C + 1))) * Real.log (C.card : ℝ) := by sorry

end ExactLearningSeparation678.Randomized.Supplement
