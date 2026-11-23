-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_neg_sqrt_log_le_sq
-- name    : Formalism.ZeroFreeDirichlet.exp_neg_sqrt_log_le_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:49.943595+00:00
-- url     : https://prove2.me/theorems/645d2322-ac45-433c-adb8-92993a767687
-- title:
--   Zero Free Dirichlet: exp neg sqrt log le sq
-- statement:
--   The Zero Free Dirichlet construction uses the exp neg sqrt log le sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/AbsZeroTermSecondDifferenceLe.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/AbsZeroTermSecondDifferenceLe.lean#L88-L93

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

theorem Formalism.ZeroFreeDirichlet.exp_neg_sqrt_log_le_sq {cs c₀ y z : ℝ} (hc0 : 0 ≤ c₀) (hcs : c₀ ≤ cs) (hy : 1 ≤ y) (hyz : y ≤ z) :
    Real.exp (-cs * Real.sqrt (Real.log z)) ≤ Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ^ 2 := by sorry
