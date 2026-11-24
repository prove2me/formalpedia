-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_POf_cW_eq
-- name    : Formalism.L2.Th1.F.POf.cW_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:19:04.267327+00:00
-- url     : https://prove2.me/theorems/e9e34b79-3124-4526-851b-0d2e33e2c0d6
-- title:
--   POf: c W eq
-- statement:
--   The POf construction uses the c W eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L14-L22

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

theorem Formalism.L2.Th1.F.POf.cW_eq (g2 g3 : K) (k : ℕ) : cW g2 g3 k =
    if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
    if 4 ≤ k then
      3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
        ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
    else 0 := by sorry
