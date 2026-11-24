-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_den_order
-- name    : Formalism.L2.Th1.F.IsogenySigmaQuotient.den_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:26.857682+00:00
-- url     : https://prove2.me/theorems/95a91665-a0c9-4cf4-9186-389c507b6fdb
-- title:
--   Isogeny Sigma Quotient: den order
-- statement:
--   The Isogeny Sigma Quotient construction uses the den order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L213-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L213-L230

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

theorem Formalism.L2.Th1.F.IsogenySigmaQuotient.den_order (hord : SigmaOrder) (he : SigmaEntire) (hb : SgStarBasic) (hα : α ≠ 0)
    (hS : ∀ P ∈ S, P ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (den L α S) z
      = 2 * ind L z + ∑ P ∈ S, (ind L (z + P) + ind L (z - P)) := by sorry
