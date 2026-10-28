-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_height_five_regions
-- name    : D1Bound5.finiteN2_height_five_regions
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:30:44.162488+00:00
-- url     : https://prove2.me/theorems/c896a1d7-6c11-4229-b531-10b235cf6f08
-- title:
--   Finite N2 height five regions
-- statement:
--   Actual ratio-refined height for the constructed finite family. The statement supplies no coefficient or height certificate: the integer rows and all five rational table margins are proved above.
-- source:
--   D1Bound5/FiniteN2RatioHeight.lean, lines 67-91, SHA-256 acd86dd6afa56a2834a76abb67f2f38aa493cf97b505b550e022ae5087305669. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN2RatioHeight_Definitions

section
noncomputable section

namespace D1Bound5
















theorem _root_.D1Bound5.finiteN2_height_five_regions (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖) <
      fiveRegionN2Height region*‖y‖^4*‖c‖^2 := by sorry

end D1Bound5
end
