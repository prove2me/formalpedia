-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_POf_pOf_split
-- name    : Formalism.L2.Th1.F.POf.pOf_split
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:18:22.170671+00:00
-- url     : https://prove2.me/theorems/60eb1e79-d7b0-4a15-a3e5-efe1b270c0be
-- title:
--   POf: p Of split
-- statement:
--   The POf construction uses the p Of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L180-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L180-L192

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F Formalism.L2.Th1.F.POf
variable {K : Type} [Field K]
variable [CharZero K]

theorem Formalism.L2.Th1.F.POf.pOf_split (g2 g3 : K) :
    pOf g2 g3 = C (g2 / 20) * X ^ 2 + C (g3 / 28) * X ^ 4
      + X ^ 6 * PowerSeries.mk fun n => coeff (n + 6) (pOf g2 g3) := by sorry
