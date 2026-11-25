-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_AddThm_hasDerivAt_P
-- name    : Formalism.L2.Th1.E.AddThm.hasDerivAt_P
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:18:27.081095+00:00
-- url     : https://prove2.me/theorems/42003d16-dfb2-4dfd-b0e6-6583ebcc0485
-- title:
--   Add Thm: has Deriv At P
-- statement:
--   The Add Thm construction uses the has Deriv At P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L16-L22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_hasDerivAt_P

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

theorem Formalism.L2.Th1.E.AddThm.hasDerivAt_P (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by sorry
