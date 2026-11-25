-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_More_map_logSer
-- name    : Formalism.L2.Th1.A.More.map_logSer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:04:10.886096+00:00
-- url     : https://prove2.me/theorems/86812d34-75b6-55fe-b215-fbcf905be344
-- title:
--   More: map log Ser
-- statement:
--   The More construction uses the map log Ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L181-L183

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
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
open More
open Formalism.L2.Th1.A.More
variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)

theorem Formalism.L2.Th1.A.More.map_logSer (W : WeierstrassCurve K) :
    PowerSeries.map φ (logSer W) = logSer (W.map φ) := by sorry
