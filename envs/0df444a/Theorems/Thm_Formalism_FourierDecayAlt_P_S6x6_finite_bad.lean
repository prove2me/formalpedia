-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_finite_bad
-- name    : Formalism.FourierDecayAlt.P.S6x6.finite_bad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:21.733518+00:00
-- url     : https://prove2.me/theorems/d8fd86c8-cd74-4fb0-bdeb-78c22aab4e23
-- title:
--   S6x6: finite bad
-- statement:
--   The S6x6 construction uses the finite bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L172-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L172-L193

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

theorem Formalism.FourierDecayAlt.P.S6x6.finite_bad {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) :
    {P : Ideal (𝓞 (maximalRealSubfield E)) | P.IsMaximal ∧ t ∉ locAt E P L}.Finite := by sorry
