-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Bridge_model_map
-- name    : Formalism.L2.Th1.A.Bridge.model_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:50.625133+00:00
-- url     : https://prove2.me/theorems/c466a452-92db-4d9e-93bb-37e93b3935a1
-- title:
--   Bridge: model map
-- statement:
--   The Bridge construction uses the model map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L44-L46

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
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
open Formalism.L2.Th1.A.Bridge
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.L2.Th1.A.Bridge.model_map (W : WeierstrassCurve K) (h : IntModel W) :
    (model W h).map (Formalism.G.unitBall K).subtype = W := by sorry
