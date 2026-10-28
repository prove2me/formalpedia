-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_height_five_regions
-- name    : D1Bound5.finiteN3_height_five_regions
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:41.863091+00:00
-- url     : https://prove2.me/theorems/2aedea11-0fbb-478c-861c-400926cc77de
-- title:
--   Finite N3 height five regions
-- statement:
--   Actual ratio-refined height for the constructed finite family. The statement supplies no coefficient or height certificate: the integer rows and all five rational table margins are proved above.
-- source:
--   D1Bound5/FiniteN3RatioHeight.lean, lines 75-99, SHA-256 3b19adaab7a046dd5d462fa93e9c3522cc668117966f660bde17388fd5b6b587. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN3RatioHeight_Definitions

section
noncomputable section

namespace D1Bound5
















theorem _root_.D1Bound5.finiteN3_height_five_regions (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN3Left x y c i‖+‖finiteN3Right x y c i‖) <
      fiveRegionN3Height region*‖y‖^7*‖c‖^3 := by sorry

end D1Bound5
end
