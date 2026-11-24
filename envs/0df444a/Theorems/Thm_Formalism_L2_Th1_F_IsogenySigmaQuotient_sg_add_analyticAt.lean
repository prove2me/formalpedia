-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_add_analyticAt
-- name    : Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_add_analyticAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:30.735918+00:00
-- url     : https://prove2.me/theorems/3c8d8be1-2f46-42a7-bc92-f698f7f66a62
-- title:
--   Isogeny Sigma Quotient: sg add analytic At
-- statement:
--   The Isogeny Sigma Quotient construction uses the sg add analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L124-L127

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
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
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)

theorem Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_add_analyticAt (hb : SgStarBasic) (P z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => sgStar L (w + P)) z := by sorry
