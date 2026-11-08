-- Prove2me | Theorems.Thm_DegreeSensitivity_degree_five_full_sensitivity_implies_goal
-- name    : DegreeSensitivity.degree_five_full_sensitivity_implies_goal
-- status  : Open
-- author  : @queelius
-- created : 2026-11-07T16:52:32.113225+00:00
-- url     : https://prove2.me/theorems/38976f97-e8b7-4af9-b2b8-e7e32b4070fc
-- title:
--   Degree five on fourteen variables suffices
-- statement:
--   If some Boolean function on 14 bits has degree at most 5, value 0 at the origin and value 1 at every unit vector, then the goal holds: some $f$ on $n > 1$ bits has $\deg f > 1$ and $s(f,\mathbf 0) > \deg(f)^{\log 6/\log 3}$.
-- source:
--   Derived: degree at most 1 is impossible for such a function, and 5^(log 6/log 3) < 14 (since 6^30 < 3^49 and 5^49 < 14^30).

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DegreeSensitivity

theorem degree_five_full_sensitivity_implies_goal
    (h : ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
      ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true) :
    ∃ (n : ℕ) (f : BoolFunc n), 1 < n ∧ 1 < polyDegree f ∧
      (polyDegree f : ℝ) ^ (Real.log 6 / Real.log 3) <
        (sensitivityAt f (fun _ => false) : ℝ) := by sorry

end DegreeSensitivity
