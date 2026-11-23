-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_mem_of_den_eq_zero
-- name    : Formalism.L2.Th1.F.IsogenySigmaQuotient.mem_of_den_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:04.288806+00:00
-- url     : https://prove2.me/theorems/a65a09c1-543c-46c7-bc38-28dbb8028eb2
-- title:
--   Isogeny Sigma Quotient: mem of den eq zero
-- statement:
--   The Isogeny Sigma Quotient construction uses the mem of den eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L282-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenySigma.lean#L282-L302

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

theorem Formalism.L2.Th1.F.IsogenySigmaQuotient.mem_of_den_eq_zero (hb : SgStarBasic) (hα : α ≠ 0) (hst : MulStable L α)
    (hS : IsKerReps L α S) (z : ℂ) (h : den L α S z = 0) : α * z ∈ L.lattice := by sorry
