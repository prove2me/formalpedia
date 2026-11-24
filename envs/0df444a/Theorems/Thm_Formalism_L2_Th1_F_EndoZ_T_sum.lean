-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sum
-- name    : Formalism.L2.Th1.F.EndoZ.T.sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:16.674401+00:00
-- url     : https://prove2.me/theorems/cc4b8cbe-4f8d-4a23-a07a-ca7cee5a80d8
-- title:
--   T: sum
-- statement:
--   The T construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L33-L45

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

theorem Formalism.L2.Th1.F.EndoZ.T.sum {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (F : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, T (f i) (F i)) : T (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, F i) := by sorry
