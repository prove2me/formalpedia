-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_half_left
-- name    : Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.herm_half_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:35.373624+00:00
-- url     : https://prove2.me/theorems/de26c258-92f0-5ad5-a82c-61078accdc61
-- title:
--   Theta Zero Hermitian Lemmas: herm half left
-- statement:
--   The Theta Zero Hermitian Lemmas construction uses the herm half left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HermHalfRight.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HermHalfRight.lean#L25-L26

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

theorem Formalism.L2.Th1.F.ThetaZeroHermitianLemmas.herm_half_left (L : PeriodPair) (x w : ℂ) : herm L (x / 2) w = herm L x w / 2 := by sorry
