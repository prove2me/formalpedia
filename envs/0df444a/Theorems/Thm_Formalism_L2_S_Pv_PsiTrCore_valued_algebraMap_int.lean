-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_valued_algebraMap_int
-- name    : Formalism.L2.S.Pv.PsiTrCore.valued_algebraMap_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:36.764479+00:00
-- url     : https://prove2.me/theorems/5e5c3041-7bfe-4dc6-8679-9fb4516b911e
-- title:
--   Psi Tr Core: valued algebra Map int
-- statement:
--   The Psi Tr Core construction uses the valued algebra Map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCoreApprox.lean#L15-L18

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

theorem Formalism.L2.S.Pv.PsiTrCore.valued_algebraMap_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (r : F)) = v.intValuation r := by sorry
