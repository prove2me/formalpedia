-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ptOf_add_generic
-- name    : Formalism.L2.Th1.E.ptOf_add_generic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:16:58.281265+00:00
-- url     : https://prove2.me/theorems/68ff84cd-5dda-5d87-9880-5518367db423
-- title:
--   E: pt Of add generic
-- statement:
--   The E construction uses the pt Of add generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L189-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L189-L220

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

theorem Formalism.L2.Th1.E.ptOf_add_generic (s t : ℂ) (hs : s ∉ L.lattice) (ht : t ∉ L.lattice) (hp : s + t ∉ L.lattice)
    (hm : s - t ∉ L.lattice) : ptOf l L ι (s + t) = ptOf l L ι s + ptOf l L ι t := by sorry
