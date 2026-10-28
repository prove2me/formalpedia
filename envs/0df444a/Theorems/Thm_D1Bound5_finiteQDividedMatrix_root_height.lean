-- Prove2me | Theorems.Thm_D1Bound5_finiteQDividedMatrix_root_height
-- name    : D1Bound5.finiteQDividedMatrix_root_height
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:42:13.434998+00:00
-- url     : https://prove2.me/theorems/2b000a30-4f24-4082-9d80-5fecea631b68
-- title:
--   Finite QDivided Matrix root height
-- statement:
--   Every one of the five actual rows satisfies the same root-column height bound. The selected nonzero integral row can therefore be used without imposing a separate height certificate.
-- source:
--   D1Bound5/FiniteQHeight.lean, lines 41-55, SHA-256 86865cf236ac82f61de86bc28514d9e3b24a1d93eff23574b7cf2a6d0efa3d7e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.finiteQDividedMatrix_root_height
    (a b s t c : ℂ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ T) (hb : ‖b‖ ≤ T) (hs : ‖s‖ ≤ T) (ht : ‖t‖ ≤ T)
    (hc : ‖c‖ ≤ C) (hTC : 1 ≤ T*C) (i : Fin 5) :
    (∑ j : Fin 4, ‖finiteQDividedMatrix a b s t c i j.succ‖) ≤ 36*T^3*C := by sorry

end D1Bound5
end
