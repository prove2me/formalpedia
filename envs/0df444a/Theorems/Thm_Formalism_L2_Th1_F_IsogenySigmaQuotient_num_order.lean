-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_num_order
-- name    : Formalism.L2.Th1.F.IsogenySigmaQuotient.num_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:11.831913+00:00
-- url     : https://prove2.me/theorems/8da95c8b-7e3a-413d-b8bb-6eae3cdca011
-- title:
--   Isogeny Sigma Quotient: num order
-- statement:
--   The Isogeny Sigma Quotient construction uses the num order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L185-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L185-L195

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

theorem Formalism.L2.Th1.F.IsogenySigmaQuotient.num_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0) (z : ℂ) :
    meromorphicOrderAt (num L α) z = 2 * ind L (α * z) := by sorry
