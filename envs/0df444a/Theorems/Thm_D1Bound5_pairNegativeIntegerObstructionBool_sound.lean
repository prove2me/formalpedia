-- Prove2me | Theorems.Thm_D1Bound5_pairNegativeIntegerObstructionBool_sound
-- name    : D1Bound5.pairNegativeIntegerObstructionBool_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:47.249242+00:00
-- url     : https://prove2.me/theorems/aa99a2ec-c3b4-444b-adae-08ff0a48b434
-- title:
--   Pair Negative Integer Obstruction Bool sound
-- statement:
--   A successful negative-integer obstruction excludes every square root. In particular, rejection cannot discard a genuine zero root.
-- source:
--   D1Bound5/PairNegativeIntegerObstruction.lean, lines 52-71, SHA-256 099be79d73801fcfb76bdc30024dc74b43ab6bdb2e935fcd75d8e115af902e02. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairNegativeIntegerObstruction_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.pairNegativeIntegerObstructionBool_sound {tau nu : ℤ}
    (z : QuadInt tau nu) (h : pairNegativeIntegerObstructionBool z = true) :
    ¬ ∃ r : QuadInt tau nu, r * r = z := by sorry

end D1Bound5
end
