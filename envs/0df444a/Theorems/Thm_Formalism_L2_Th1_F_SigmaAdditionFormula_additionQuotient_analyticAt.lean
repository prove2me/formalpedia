-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_analyticAt
-- name    : Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_analyticAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:41.685184+00:00
-- url     : https://prove2.me/theorems/8b15b9e8-29fd-4293-a45c-3fd209f3fd31
-- title:
--   Sigma Addition Formula: addition Quotient analytic At
-- statement:
--   The Sigma Addition Formula construction uses the addition Quotient analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L160-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L160-L177

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

theorem Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_analyticAt (he : SigmaEntire) (hz : SigmaZero) (z : ℂ) (hzL : z ∉ L.lattice) :
    AnalyticAt ℂ (additionQuotient L w) z := by sorry
