-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_one_tmul_mem
-- name    : Formalism.L2.S.Pv.PsiTrCore.one_tmul_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:57:47.767807+00:00
-- url     : https://prove2.me/theorems/ec9ea9eb-6798-4989-8a78-7db357208f0d
-- title:
--   Psi Tr Core: one tmul mem
-- statement:
--   The Psi Tr Core construction uses the one tmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCore.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCore.lean#L23-L29

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreTrace
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Formalism.L2.S.Pv.PsiTrCore.one_tmul_mem (c : Af F) (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] c ∈ IntAf F E := by sorry
