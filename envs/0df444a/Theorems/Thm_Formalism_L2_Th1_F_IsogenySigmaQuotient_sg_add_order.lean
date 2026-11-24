-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_add_order
-- name    : Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_add_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:33.189378+00:00
-- url     : https://prove2.me/theorems/bf3545f9-3dff-4ffc-bba1-498615ac7e4d
-- title:
--   Isogeny Sigma Quotient: sg add order
-- statement:
--   The Isogeny Sigma Quotient construction uses the sg add order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L112-L116

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

theorem Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_add_order (hord : SigmaOrder) (he : SigmaEntire) (P z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => sgStar L (w + P)) z = ind L (z + P) := by sorry
