-- Prove2me | Theorems.Thm_D1Bound5_two_small_large_T_lower_window_impossible
-- name    : D1Bound5.two_small_large_T_lower_window_impossible
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:15.371088+00:00
-- url     : https://prove2.me/theorems/0ecd82c0-b878-4a90-afc3-9e83906781c1
-- title:
--   Two small large T lower window impossible
-- statement:
--   Auxiliary result `two_small_large_T_lower_window_impossible` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallLargeTScalar.lean, lines 6-22, SHA-256 1b6203efdcea0221de771d1a60328cc585980bd3f0ccf1c486409156e649ed47. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5

theorem _root_.D1Bound5.two_small_large_T_lower_window_impossible
    (B S T C : ℝ) (hB : 0 < B) (hB3 : B < 3) (hS : 0 < S)
    (hS8 : S < (10 : ℝ)^8) (hT : (10 : ℝ)^72 ≤ T) (hTC : T ≤ C) :
    ¬ C < 101*B^2*S^4/T := by sorry







end D1Bound5
end
