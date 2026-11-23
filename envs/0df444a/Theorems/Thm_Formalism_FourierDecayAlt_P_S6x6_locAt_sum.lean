-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_locAt_sum
-- name    : Formalism.FourierDecayAlt.P.S6x6.locAt_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:35.54474+00:00
-- url     : https://prove2.me/theorems/f77be63f-5a4a-4d08-9c7c-6e819a1196c1
-- title:
--   S6x6: loc At sum
-- statement:
--   The S6x6 construction uses the loc At sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L105-L109

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

theorem Formalism.FourierDecayAlt.P.S6x6.locAt_sum {L : Submodule ℤ E} (hL : IsFLattice E L)
    {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) {ι : Type*} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, f i ∈ locAt E P L) : ∑ i ∈ s, f i ∈ locAt E P L := by sorry
