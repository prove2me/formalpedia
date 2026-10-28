-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_height_scaled
-- name    : D1Bound5.finiteN2_height_scaled
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:16.363705+00:00
-- url     : https://prove2.me/theorems/c0023782-852b-42ee-a940-51452153f228
-- title:
--   Finite N2 height scaled
-- statement:
--   Actual N2 root-column height, with the paper's sharp constant.
-- source:
--   D1Bound5/FiniteN2Height.lean, lines 81-92, SHA-256 2243c6283cc2715ea06a1ac894af3fc0ea0e8e3a907fae2e4dc3a502c1037c77. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
namespace D1Bound5
















theorem _root_.D1Bound5.finiteN2_height_scaled (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖) <
      243*‖y‖^4*‖c‖^2 := by sorry

end D1Bound5
end
