-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_absNorm_inv_mul_different
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.absNorm_inv_mul_different
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:06.667548+00:00
-- url     : https://prove2.me/theorems/65dec0ef-7ec6-4c79-9486-f75fff7d5983
-- title:
--   B5: abs Norm inv mul different
-- statement:
--   The B5 construction uses the abs Norm inv mul different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/AbsNormInvMulDifferent.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/AbsNormInvMulDifferent.lean#L15-L33

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_AbsNormInvMulDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.absNorm_inv_mul_different (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
    [Algebra K E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E))
    (h : differentIdeal (𝓞 K) (𝓞 E) = 𝔟 * (c • 𝔟)) :
    FractionalIdeal.absNorm (((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ *
        ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ^ 2 =
      (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) : ℚ) := by sorry
