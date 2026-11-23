-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_exists_real_mem_different
-- name    : Formalism.FourierDecayAlt.P.S6x6.exists_real_mem_different
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:49.446392+00:00
-- url     : https://prove2.me/theorems/8acc3dd2-0a10-481b-84ca-bf0de56241ec
-- title:
--   S6x6: exists real mem different
-- statement:
--   The S6x6 construction uses the exists real mem different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L14-L40

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

theorem Formalism.FourierDecayAlt.P.S6x6.exists_real_mem_different (g : ℕ) (hc : PrimeToDifferent E g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsPrime)
    (hgP : (g : 𝓞 (maximalRealSubfield E)) ∈ P) :
    ∃ a : 𝓞 (maximalRealSubfield E), a ∉ P ∧
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a ∈ differentIdeal ℤ (𝓞 E) := by sorry
