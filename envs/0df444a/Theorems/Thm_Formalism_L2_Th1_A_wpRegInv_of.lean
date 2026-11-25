-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_wpRegInv_of
-- name    : Formalism.L2.Th1.A.wpRegInv_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:18.620977+00:00
-- url     : https://prove2.me/theorems/3efa0e13-dd51-4bc7-9134-9928904fe632
-- title:
--   A: wp Reg Inv of
-- statement:
--   The A construction uses the wp Reg Inv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeK.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeK.lean#L165-L171

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A

theorem Formalism.L2.Th1.A.wpRegInv_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : WpRegInv := by sorry
