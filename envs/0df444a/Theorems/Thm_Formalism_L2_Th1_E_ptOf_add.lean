-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ptOf_add
-- name    : Formalism.L2.Th1.E.ptOf_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:52.25524+00:00
-- url     : https://prove2.me/theorems/2d73d19f-1b79-5357-b53d-f647fb6452b3
-- title:
--   E: pt Of add
-- statement:
--   The E construction uses the pt Of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L222-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L222-L261

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
variable [DecidableEq ℂ_[l]]

theorem Formalism.L2.Th1.E.ptOf_add (s t : ℂ) : ptOf l L ι (s + t) = ptOf l L ι s + ptOf l L ι t := by sorry
