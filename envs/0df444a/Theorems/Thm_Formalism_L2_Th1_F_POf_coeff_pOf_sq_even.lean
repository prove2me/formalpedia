-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_POf_coeff_pOf_sq_even
-- name    : Formalism.L2.Th1.F.POf.coeff_pOf_sq_even
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:35.949812+00:00
-- url     : https://prove2.me/theorems/851cd7db-c457-4751-9127-df5ab8a645dc
-- title:
--   POf: coeff p Of sq even
-- statement:
--   The POf construction uses the coeff p Of sq even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassNumeratorDenominator.lean#L65-L81

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

theorem Formalism.L2.Th1.F.POf.coeff_pOf_sq_even (g2 g3 : K) (m : ℕ) :
    coeff (2 * m) (pOf g2 g3 ^ 2)
      = ∑ a ∈ Finset.range (m + 1), cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1) := by sorry
