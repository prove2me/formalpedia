-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_intAf_le_congSub
-- name    : Formalism.L2.S.Pv.PsiTrCore.intAf_le_congSub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:57:17.256797+00:00
-- url     : https://prove2.me/theorems/8ad5a16e-2cb2-4e0b-b1fb-41bd5765193e
-- title:
--   Psi Tr Core: int Af le cong Sub
-- statement:
--   The Psi Tr Core construction uses the int Af le cong Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCore.lean#L55-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/PsiTrCore.lean#L55-L103

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

theorem Formalism.L2.S.Pv.PsiTrCore.intAf_le_congSub (n : ℤ) (hn : n ≠ 0) : IntAf F E ≤ congSub n := by sorry
