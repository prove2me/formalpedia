-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_exists_decomp
-- name    : Formalism.L2.S.Pv.PsiTrCore.exists_decomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:25.108946+00:00
-- url     : https://prove2.me/theorems/2eb33dbe-344c-4974-88b3-ec2fde153360
-- title:
--   Psi Tr Core: exists decomp
-- statement:
--   The Psi Tr Core construction uses the exists decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L165-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L165-L191

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.L2.S.Pv.PsiTrCore.exists_decomp (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧
      a = algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (n : F) * c := by sorry
