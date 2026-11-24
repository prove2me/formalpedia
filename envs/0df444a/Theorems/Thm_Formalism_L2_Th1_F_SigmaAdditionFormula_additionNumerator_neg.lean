-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionNumerator_neg
-- name    : Formalism.L2.Th1.F.SigmaAdditionFormula.additionNumerator_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:48.541439+00:00
-- url     : https://prove2.me/theorems/ea4d9e47-ebd1-4e61-915e-5ec6f1bd5371
-- title:
--   Sigma Addition Formula: addition Numerator neg
-- statement:
--   The Sigma Addition Formula construction uses the addition Numerator neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L60-L64

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)

theorem Formalism.L2.Th1.F.SigmaAdditionFormula.additionNumerator_neg (ho : SigmaOdd) (z : ℂ) : frobeniusStickelbergerDetMulSigmaCube L w (-z) = frobeniusStickelbergerDetMulSigmaCube L w z := by sorry
