-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_nS
-- name    : Formalism.L2.Th1.A.Plus.toL_nS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:32.412611+00:00
-- url     : https://prove2.me/theorems/4dcc5f19-5ee8-41a9-8670-46d62f7cebda
-- title:
--   Plus: to L n S
-- statement:
--   The Plus construction uses the to L n S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ToLTDenMulInv.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ToLTDenMulInv.lean#L80-L84

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Plus
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

theorem Formalism.L2.Th1.A.Plus.toL_nS : toL (nS W xP yP) =
    HahnSeries.C (W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * toL X * toL (xS W)
      - HahnSeries.C (2 * yP + W.a₁ * xP + W.a₃) * toL (yS W)
      + HahnSeries.C (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3) * toL X ^ 3 := by sorry
