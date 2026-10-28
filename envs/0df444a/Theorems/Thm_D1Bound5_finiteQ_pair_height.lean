-- Prove2me | Theorems.Thm_D1Bound5_finiteQ_pair_height
-- name    : D1Bound5.finiteQ_pair_height
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:15.829328+00:00
-- url     : https://prove2.me/theorems/8ef8db40-ac7a-412e-9b40-fccece07ee05
-- title:
--   Finite Q pair height
-- statement:
--   The actual two polynomial root weights have total height at most the sum of their 36 absolute integer coefficients.
-- source:
--   D1Bound5/FiniteQHeight.lean, lines 10-39, SHA-256 86865cf236ac82f61de86bc28514d9e3b24a1d93eff23574b7cf2a6d0efa3d7e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.finiteQ_pair_height
    (u v c : ℂ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hu : ‖u‖ ≤ T) (hv : ‖v‖ ≤ T) (hc : ‖c‖ ≤ C) (hTC : 1 ≤ T*C) :
    ‖finiteQLeft u v c‖ + ‖finiteQRight u v c‖ ≤ 36*T^3*C := by sorry



end D1Bound5
end
