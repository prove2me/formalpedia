-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_log_deriv_differentiableAt
-- name    : Formalism.ZeroFreeDirichlet.neg_log_deriv_differentiableAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:39.606213+00:00
-- url     : https://prove2.me/theorems/f839df08-ac8a-4e66-a18f-9e67b3c83cba
-- title:
--   Zero Free Dirichlet: neg log deriv differentiable At
-- statement:
--   The Zero Free Dirichlet construction uses the neg log deriv differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean#L10-L17

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

theorem Formalism.ZeroFreeDirichlet.neg_log_deriv_differentiableAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℂ}
    (hL : DirichletCharacter.LFunction χ w ≠ 0) : DifferentiableAt ℂ (negLD χ) w := by sorry
