-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_POf_cW_rec
-- name    : Formalism.L2.Th1.F.POf.cW_rec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:56.919677+00:00
-- url     : https://prove2.me/theorems/98ec152b-5a82-41c1-ac4a-71975c0fe6b7
-- title:
--   POf: c W rec
-- statement:
--   The POf construction uses the c W rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L28-L42

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

theorem Formalism.L2.Th1.F.POf.cW_rec (g2 g3 : K) (m : ℕ) (hm : 2 ≤ m) : cW g2 g3 (m + 2) =
    3 / ((2 * ((m + 2 : ℕ) : K) + 1) * (((m + 2 : ℕ) : K) - 3)) *
      ∑ a ∈ Finset.range (m + 1), cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1) := by sorry
