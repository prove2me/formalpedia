-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_valued_algebraMap
-- name    : Formalism.L2.S.Pv.PsiTrCore.valued_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:22.589568+00:00
-- url     : https://prove2.me/theorems/135f51be-f9f1-4043-bc51-8a218e50b7a0
-- title:
--   Psi Tr Core: valued algebra Map
-- statement:
--   The Psi Tr Core construction uses the valued algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L11-L13

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

theorem Formalism.L2.S.Pv.PsiTrCore.valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by sorry
