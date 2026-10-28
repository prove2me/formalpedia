-- Prove2me | Theorems.Thm_D1Bound5_finiteA3_height_five_regions
-- name    : D1Bound5.finiteA3_height_five_regions
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:19:26.171276+00:00
-- url     : https://prove2.me/theorems/68f2427c-bd36-40ec-bf4d-2c630f2440b2
-- title:
--   Finite A3 height five regions
-- statement:
--   Actual ratio-refined height for the constructed finite family. The statement supplies no coefficient or height certificate: the integer rows and all five rational table margins are proved above.
-- source:
--   D1Bound5/FiniteA3RatioHeight.lean, lines 62-86, SHA-256 747d84efb3a599bfd5fb9dfc2190b17d3fd8f676687d8e8b401785ccf8d1c7d7. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA3RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5












theorem _root_.D1Bound5.finiteA3_height_five_regions (region : Fin 5) (x y c : ℂ)
    (hy : y ≠ 0) (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖)
    (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA3Left x y c i‖+‖finiteA3Right x y c i‖) <
      fiveRegionA3Height region*‖y‖^6*‖c‖^3 := by sorry

end D1Bound5
end
