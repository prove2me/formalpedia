-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_abs_zero_term_second_difference_le
-- name    : Formalism.ZeroFreeDirichlet.abs_zero_term_second_difference_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:16.483518+00:00
-- url     : https://prove2.me/theorems/d45cebd1-534e-4620-abf0-329ebfc47ba3
-- title:
--   Zero Free Dirichlet: abs zero term second difference le
-- statement:
--   The Zero Free Dirichlet construction uses the abs zero term second difference le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/AbsZeroTermSecondDifferenceLe.lean#L21-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/AbsZeroTermSecondDifferenceLe.lean#L21-L66

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
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

theorem Formalism.ZeroFreeDirichlet.abs_zero_term_second_difference_le {y h β : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (_hh1 : h ≤ 1) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β < 1) :
    |(y * (1 + h)) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
        + y * h * (y ^ β / β)| ≤ 2 * y ^ 2 * h ^ 2 := by sorry
