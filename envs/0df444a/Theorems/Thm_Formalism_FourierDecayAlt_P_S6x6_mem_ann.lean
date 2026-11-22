-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_mem_ann
-- name    : Formalism.FourierDecayAlt.P.S6x6.mem_ann
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:43.877463+00:00
-- url     : https://prove2.me/theorems/678a97d0-c5a0-483f-8b99-0357b329d2e7
-- title:
--   S6x6: mem ann
-- statement:
--   The S6x6 construction uses the mem ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L121-L123

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

theorem Formalism.FourierDecayAlt.P.S6x6.mem_ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (a : 𝓞 (maximalRealSubfield E)) :
    a ∈ ann hL t ↔ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L := by sorry
