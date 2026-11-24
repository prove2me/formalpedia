-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_exists_int_near
-- name    : Formalism.L2.S.Pv.PsiTrCore.exists_int_near
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:59.676872+00:00
-- url     : https://prove2.me/theorems/8b65b016-2f37-495a-96b1-68bfbfb416cd
-- title:
--   Psi Tr Core: exists int near
-- statement:
--   The Psi Tr Core construction uses the exists int near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L71-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L71-L115

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

theorem Formalism.L2.S.Pv.PsiTrCore.exists_int_near (v : HeightOneSpectrum (𝓞 F)) (a w : v.adicCompletion F)
    (ha : Valued.v a ≤ 1) (hw : w ≠ 0) (hw1 : Valued.v w ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (r : F)) < Valued.v w := by sorry
