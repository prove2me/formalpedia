-- Prove2me | Theorems.Thm_CrossingConsequences_unit_distance_upper_bound
-- name    : CrossingConsequences.unit_distance_upper_bound
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T17:33:08.617364+00:00
-- url     : https://prove2.me/theorems/e78325c8-7d34-4a91-8b2d-53e64c295a62
-- title:
--   Unit-distance upper bound with exponent $4/3$
-- statement:
--   For every finite point set P in the standard Euclidean plane, let u(P) be the number of unordered pairs of distinct points at Euclidean distance exactly 1. There is a single positive real constant C, independent of P, such that
--
--   $$u(P) \le C|P|^{4/3}.$$
--
--   The quantifier includes empty and singleton point sets. This is the classical upper-bound statement; it does not assert that the exponent is optimal.
-- source:
--   J. Spencer, E. Szemerédi, and W. T. Trotter, Jr., “Unit distances in the Euclidean plane,” in B. Bollobás (ed.), Graph Theory and Combinatorics (Cambridge, 1983), Academic Press, 1984, pp. 293–303. Primary text: https://trotter.math.gatech.edu/papers/44.pdf. Lean formal statement: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/unit_distance_upper_bound.lean#L6-L10; counting definition: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/unitDist.lean#L6-L9; project proof: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/paper/crossing_bounds.tex#L79-L85.

import Definitions.Def_unitDist
open scoped Real

namespace CrossingConsequences
theorem unit_distance_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        (unitDist P : ℝ) ≤ C * (P.card : ℝ) ^ ((4 : ℝ) / 3) := by sorry
end CrossingConsequences
