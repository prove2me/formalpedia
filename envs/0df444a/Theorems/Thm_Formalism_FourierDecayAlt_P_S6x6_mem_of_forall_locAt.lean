-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_mem_of_forall_locAt
-- name    : Formalism.FourierDecayAlt.P.S6x6.mem_of_forall_locAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:35.76114+00:00
-- url     : https://prove2.me/theorems/26ca2384-4344-4b2a-bd2f-426f499b0d57
-- title:
--   S6x6: mem of forall loc At
-- statement:
--   The S6x6 construction uses the mem of forall loc At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L195-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L195-L206

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}

theorem Formalism.FourierDecayAlt.P.S6x6.mem_of_forall_locAt {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (ht : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ locAt E P L) : t ∈ L := by sorry
