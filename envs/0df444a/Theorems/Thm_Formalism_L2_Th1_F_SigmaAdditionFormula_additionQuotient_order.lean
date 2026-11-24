-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_order
-- name    : Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:19.086657+00:00
-- url     : https://prove2.me/theorems/0225879f-1fb1-4169-96e6-fc516445645b
-- title:
--   Sigma Addition Formula: addition Quotient order
-- statement:
--   The Sigma Addition Formula construction uses the addition Quotient order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L206-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L206-L222

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

theorem Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_order (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple)
    (hq : SigmaQuasi) (hord : SigmaOrder) (z : ℂ) : 0 ≤ meromorphicOrderAt (additionQuotient L w) z := by sorry
