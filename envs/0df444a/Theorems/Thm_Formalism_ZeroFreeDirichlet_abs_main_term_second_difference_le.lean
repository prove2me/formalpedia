-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_abs_main_term_second_difference_le
-- name    : Formalism.ZeroFreeDirichlet.abs_main_term_second_difference_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:16.905185+00:00
-- url     : https://prove2.me/theorems/450b4822-3b5b-4248-84c7-fbbb6b32a876
-- title:
--   Zero Free Dirichlet: abs main term second difference le
-- statement:
--   The Zero Free Dirichlet construction uses the abs main term second difference le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/AbsZeroTermSecondDifferenceLe.lean#L68-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/AbsZeroTermSecondDifferenceLe.lean#L68-L86

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

theorem Formalism.ZeroFreeDirichlet.abs_main_term_second_difference_le {y h γ : ℝ} (hy : 0 < y) (hh : 0 < h) :
    |y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y| ≤ y ^ 2 * h ^ 2 := by sorry
