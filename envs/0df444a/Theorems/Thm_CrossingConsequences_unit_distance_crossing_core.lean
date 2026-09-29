-- Prove2me | Theorems.Thm_CrossingConsequences_unit_distance_crossing_core
-- name    : CrossingConsequences.unit_distance_crossing_core
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T18:26:05.234066+00:00
-- url     : https://prove2.me/theorems/26574b7f-cf62-43e2-9b66-d7da1c460d37
-- title:
--   Unit-distance crossing core
-- statement:
--   This composite interface isolates the numerical consequence used in the planar unit-distance upper bound. For every finite point set $P$ in the Euclidean plane, there is a natural number $e$ such that
--
--   $$
--   \operatorname{unitDist}(P)-|P|\le e,
--   $$
--
--   and, whenever $4|P|\le e$,
--
--   $$
--   \frac{e^3}{100|P|^2}\le 2|P|^2.
--   $$
--
--   Here $\operatorname{unitDist}(P)$ is the unit-distance count and $|P|$ is the cardinality of $P$. The number $e$ is the edge-count quantity supplied by the unit-distance crossing construction. This theorem is the reusable bridge consumed by the headline numerical argument: it packages the geometric graph and crossing estimates while exposing exactly the arithmetic interface needed downstream.
-- source:
--   Composite bridge derived from J. Spencer, E. Szemerédi, and W. T. Trotter, Jr., “Unit distances in the Euclidean plane,” in B. Bollobás (ed.), Graph Theory and Combinatorics (Cambridge, 1983), Academic Press, 1984, pp. 293–303; primary text: https://trotter.math.gatech.edu/papers/44.pdf. Upstream formalization: wpegden/crossing-consequences at commit 8769d142033fce042f502bf2857afb6b1375b5c3, https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/unit_distance_upper_bound.lean (numerical interface), with the count definition at https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/unitDist.lean.

import Definitions.Def_unitDist
open scoped Real

namespace CrossingConsequences

theorem unit_distance_crossing_core :
    ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      ∃ e : ℕ,
        (unitDist P : ℝ) - (P.card : ℝ) ≤ (e : ℝ) ∧
        (4 * P.card ≤ e →
          (e : ℝ) ^ 3 / (100 * (P.card : ℝ) ^ 2) ≤
            2 * (P.card : ℝ) ^ 2) := by sorry

end CrossingConsequences
