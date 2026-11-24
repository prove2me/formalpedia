-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EndoZ_clause3
-- name    : Formalism.L2.Th1.F.EndoZ.clause3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:08.575865+00:00
-- url     : https://prove2.me/theorems/678b885b-8795-4238-9509-d3d2da8489c7
-- title:
--   Endo Z: clause3
-- statement:
--   The Endo Z construction uses the clause3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L121-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L121-L143

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp

theorem Formalism.L2.Th1.F.EndoZ.clause3 (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (hα : α ≠ 0) (hm : MulStable L α)
    (hS : IsKerReps L α S) :
    C (α ^ 2) * rescale α (pSeries L) = pSeries L
      + ∑ P : S, (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - C (L.weierstrassP (P : ℂ))) := by sorry
