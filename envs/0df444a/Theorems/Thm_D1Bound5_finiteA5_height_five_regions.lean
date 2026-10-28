-- Prove2me | Theorems.Thm_D1Bound5_finiteA5_height_five_regions
-- name    : D1Bound5.finiteA5_height_five_regions
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:28.634953+00:00
-- url     : https://prove2.me/theorems/cb29746a-f938-4903-9c7e-4f6262dacc31
-- title:
--   Finite A5 height five regions
-- statement:
--   Actual ratio-refined height for the constructed finite family. The statement supplies no coefficient or height certificate: the integer rows and all five rational table margins are proved above.
-- source:
--   D1Bound5/FiniteA5RatioHeight.lean, lines 77-101, SHA-256 caf61348fb66d8b422dc583b23aa54e12391df9c8ee1e7521aa8bfee1537daef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5












theorem _root_.D1Bound5.finiteA5_height_five_regions (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA5Left x y c i‖+‖finiteA5Right x y c i‖) <
      fiveRegionA5Height region*‖y‖^12*‖c‖^5 := by sorry

end D1Bound5
end
