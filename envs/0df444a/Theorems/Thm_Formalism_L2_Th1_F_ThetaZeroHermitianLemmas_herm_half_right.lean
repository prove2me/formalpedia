-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_half_right
-- name    : Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.herm_half_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:15.305699+00:00
-- url     : https://prove2.me/theorems/3a054a91-87c9-57a1-a4f4-bcf8ade2dea7
-- title:
--   Theta Zero Hermitian Lemmas: herm half right
-- statement:
--   The Theta Zero Hermitian Lemmas construction uses the herm half right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HermHalfRight.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HermHalfRight.lean#L22-L23

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThetaZeroHermitianLemmas

theorem Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.herm_half_right (L : PeriodPair) (x w : ℂ) : herm L x (w / 2) = herm L x w / 2 := by sorry
