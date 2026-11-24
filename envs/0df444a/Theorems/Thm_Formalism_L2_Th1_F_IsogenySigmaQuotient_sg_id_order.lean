-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_id_order
-- name    : Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_id_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:12.320164+00:00
-- url     : https://prove2.me/theorems/62e0a42b-9856-4e53-9a31-e0fefb707b9c
-- title:
--   Isogeny Sigma Quotient: sg id order
-- statement:
--   The Isogeny Sigma Quotient construction uses the sg id order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L153-L157

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

theorem Formalism.L2.Th1.F.IsogenySigmaQuotient.sg_id_order (hord : SigmaOrder) (he : SigmaEntire) (z : ℂ) :
    meromorphicOrderAt (sgStar L) z = ind L z := by sorry
