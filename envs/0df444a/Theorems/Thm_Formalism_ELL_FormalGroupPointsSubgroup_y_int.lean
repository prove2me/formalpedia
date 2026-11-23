-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_y_int
-- name    : Formalism.ELL.FormalGroupPointsSubgroup.y_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:34.774029+00:00
-- url     : https://prove2.me/theorems/fc7a9b29-ad5e-44db-a717-cd3beff11993
-- title:
--   Formal Group Points Subgroup: y int
-- statement:
--   The Formal Group Points Subgroup construction uses the y int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L32-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L32-L53

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsSubgroup
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.FormalGroupPointsSubgroup.y_int (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 := by sorry
