-- Prove2me | Theorems.Thm_D1Bound5_finiteA4_height_five_regions
-- name    : D1Bound5.finiteA4_height_five_regions
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:32:48.466362+00:00
-- url     : https://prove2.me/theorems/ca9455a8-fa07-4d8b-a82b-4172a30916a5
-- title:
--   Finite A4 height five regions
-- statement:
--   Actual ratio-refined height for the constructed finite family. The statement supplies no coefficient or height certificate: the integer rows and all five rational table margins are proved above.
-- source:
--   D1Bound5/FiniteA4RatioHeight.lean, lines 69-93, SHA-256 a98d9593d896e1b8a0048726d24791b93b2bacc8fb14d4196e608cc3b8ddd02c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA4RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5












theorem _root_.D1Bound5.finiteA4_height_five_regions (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA4Left x y c i‖+‖finiteA4Right x y c i‖) <
      fiveRegionA4Height region*‖y‖^9*‖c‖^4 := by sorry

end D1Bound5
end
