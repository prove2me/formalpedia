-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_partial_sum_norm_le_near_one
-- name    : Formalism.ZeroFreeDirichlet.partial_sum_norm_le_near_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:43:09.169826+00:00
-- url     : https://prove2.me/theorems/b2ff4d2f-58a3-4f27-a8fd-5865b612aec1
-- title:
--   Zero Free Dirichlet: partial sum norm le near one
-- statement:
--   The Zero Free Dirichlet construction uses the partial sum norm le near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L63-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L63-L87

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.partial_sum_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) :
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (1 + Real.log (3 * q)) := by sorry
