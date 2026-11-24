-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_integrand_differentiableAt
-- name    : Formalism.ZeroFreeDirichlet.perron_integrand_differentiableAt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:09.88452+00:00
-- url     : https://prove2.me/theorems/e45f9547-fb9c-46bc-86da-d35324852d59
-- title:
--   Zero Free Dirichlet: perron integrand differentiable At
-- statement:
--   The Zero Free Dirichlet construction uses the perron integrand differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean#L19-L25

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.perron_integrand_differentiableAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) (hL : DirichletCharacter.LFunction χ w ≠ 0) :
    DifferentiableAt ℂ (Fchi χ y) w := by sorry
