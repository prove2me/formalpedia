-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Q2_subst_neg_X
-- name    : Formalism.L2.Th1.A.Q2.subst_neg_X
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:26:44.266385+00:00
-- url     : https://prove2.me/theorems/50c66701-eba1-42c5-a26f-80d55039dc16
-- title:
--   Q2: subst neg X
-- statement:
--   The Q2 construction uses the subst neg X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/NormLeOneOfMonicTwo.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/NormLeOneOfMonicTwo.lean#L18-L19

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
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.Q2.subst_neg_X (f : R⟦X⟧) : f.subst (-X : R⟦X⟧) = rescale (-1) f := by sorry
