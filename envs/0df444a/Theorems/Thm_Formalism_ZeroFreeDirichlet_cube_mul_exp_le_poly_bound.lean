-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_cube_mul_exp_le_poly_bound
-- name    : Formalism.ZeroFreeDirichlet.cube_mul_exp_le_poly_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:55.879818+00:00
-- url     : https://prove2.me/theorems/265a578c-5421-4ea6-9736-5db3ae4c9ca9
-- title:
--   Zero Free Dirichlet: cube mul exp le poly bound
-- statement:
--   The Zero Free Dirichlet construction uses the cube mul exp le poly bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L94-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L94-L122

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

theorem Formalism.ZeroFreeDirichlet.cube_mul_exp_le_poly_bound (c₁ s y X : ℝ) (hc₁ : 0 < c₁) (hs0 : 0 < s) (hy0 : 0 < y)
    (hX : X = Real.exp (-(c₁ * s / 2))) :
    s ^ 3 * X * y ≤ 6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s)) := by sorry
