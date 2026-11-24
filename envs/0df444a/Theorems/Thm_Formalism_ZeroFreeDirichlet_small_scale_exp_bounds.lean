-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_small_scale_exp_bounds
-- name    : Formalism.ZeroFreeDirichlet.small_scale_exp_bounds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:25.694057+00:00
-- url     : https://prove2.me/theorems/49283726-2dad-4074-90b8-d925710b163c
-- title:
--   Zero Free Dirichlet: small scale exp bounds
-- statement:
--   The Zero Free Dirichlet construction uses the small scale exp bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExpGainFromZeroFreeRegion.lean#L84-L92

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

theorem Formalism.ZeroFreeDirichlet.small_scale_exp_bounds (c₁ s : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (hs : s < 10) :
    Real.exp (c₁ * s / 2) ≤ 3 ∧ 1 ≤ 3 * Real.exp (-(c₁ / 4) * s) := by sorry
