-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_AddThm_P_sub_ne
-- name    : Formalism.L2.Th1.E.AddThm.P_sub_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:06:09.226265+00:00
-- url     : https://prove2.me/theorems/f7fb8ecd-11b3-55f9-8451-5be5e02a0b45
-- title:
--   Add Thm: P sub ne
-- statement:
--   The Add Thm construction uses the P sub ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L28-L33

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
open Formalism.L2.Th1.E.AddThm
open Formalism.L2.Th1
variable (L : PeriodPair)

theorem Formalism.L2.Th1.E.AddThm.P_sub_ne (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hp : z + w ∉ L.lattice)
    (hm : z - w ∉ L.lattice) : L.weierstrassP z - L.weierstrassP w ≠ 0 := by sorry
