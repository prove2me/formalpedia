-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_gain_from_zero_free_region
-- name    : Formalism.ZeroFreeDirichlet.exp_gain_from_zero_free_region
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:36.034091+00:00
-- url     : https://prove2.me/theorems/4632e07e-c95f-4a50-8396-bdccd8794c81
-- title:
--   Zero Free Dirichlet: exp gain from zero free region
-- statement:
--   The Zero Free Dirichlet construction uses the exp gain from zero free region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L70-L82

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ChebyshevCharacterExplicitGeneral
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExpGainFromZeroFreeRegion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.exp_gain_from_zero_free_region (y s c₁ σ₁ L : ℝ) (hy0 : 0 < y) (hℓ : Real.log y = s ^ 2) (hs0 : 0 < s)
    (hc₁ : 0 < c₁) (hL : 0 < L) (hL4 : 4 * L ≤ s) (hσ : σ₁ ≤ 1 - c₁ / (4 * L)) :
    Real.exp (c₁ * s / 2) * y ^ σ₁ ≤ y * Real.exp (-(c₁ * s / 2)) := by sorry
