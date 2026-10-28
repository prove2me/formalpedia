-- Prove2me | Theorems.Thm_D1Bound5_finiteA5_five_region_height_slack
-- name    : D1Bound5.finiteA5_five_region_height_slack
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:21:03.343859+00:00
-- url     : https://prove2.me/theorems/22e9295e-c459-44cb-bec3-65d49df3ae84
-- title:
--   Finite A5 five region height slack
-- statement:
--   The five displayed coefficient constants are checked directly from the actual integer coefficient vectors at their exact rational anchor ratios.
-- source:
--   D1Bound5/FiniteA5RatioHeight.lean, lines 65-75, SHA-256 caf61348fb66d8b422dc583b23aa54e12391df9c8ee1e7521aa8bfee1537daef. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5









set_option maxHeartbeats 4000000 in

theorem _root_.D1Bound5.finiteA5_five_region_height_slack (region : Fin 5) (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 6,
      finiteA5RatioWeights (fiveRegionAnchorRatio region) i ell/(1000 : ℝ)^(5-(ell : ℕ))) <
      fiveRegionA5Height region := by sorry



end D1Bound5
end
