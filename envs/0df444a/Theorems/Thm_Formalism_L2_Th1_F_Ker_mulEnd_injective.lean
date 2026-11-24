-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Ker_mulEnd_injective
-- name    : Formalism.L2.Th1.F.Ker.mulEnd_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:01.075086+00:00
-- url     : https://prove2.me/theorems/f02813ab-1d41-4ba3-b85e-c62d9519637b
-- title:
--   Ker: mul End injective
-- statement:
--   The Ker construction uses the mul End injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MulStableIntegral.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MulStableIntegral.lean#L83-L88

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
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
open Formalism.L2.Th1.F.Ker

theorem Formalism.L2.Th1.F.Ker.mulEnd_injective (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    Function.Injective (mulEnd L α h) := by sorry
