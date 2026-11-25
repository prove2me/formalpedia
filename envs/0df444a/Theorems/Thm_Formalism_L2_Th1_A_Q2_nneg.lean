-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Q2_nneg
-- name    : Formalism.L2.Th1.A.Q2.nneg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:25:03.71581+00:00
-- url     : https://prove2.me/theorems/c8112752-b083-49af-a79b-6f2f85cc0d40
-- title:
--   Q2: nneg
-- statement:
--   The Q2 construction uses the nneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/NormLeOneOfMonicTwo.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/NormLeOneOfMonicTwo.lean#L42-L44

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
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
open Formalism.L2.Th1.A.Q2
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.L2.Th1.A.Q2.nneg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by sorry
