-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB24_interior_caplinear_global_secant
-- name    : AvramDividend.Classical.avram_gbB24_interior_caplinear_global_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:53:44.292348+00:00
-- url     : https://prove2.me/theorems/db60b97d-f48c-4493-8dd2-53189f470bb9
-- title:
--   Interior cap-linear extension preserves global unit-slope secant domination
-- statement:
--   If the intrinsic value w has secant slopes at least one on the nonnegative interval below b, its continuation with unit slope for arguments above b has secant slopes at least one for all 0<=s<=t, including segments crossing b. This is the deterministic cap-independent signed dividend control used in the stopped original Ito-Stieltjes finite-cap proof.
-- source:
--   Lattice case split at interior cap b and lower secant inequality; prepares admissible-cap-C dividend control at a stricter interior clipping b without incorrectly strengthening IsAdmissibleLe.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_gbB24_interior_caplinear_global_secant
    (w : ℝ → ℝ) (b : ℝ)
    (hsec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ b → t - s ≤ w t - w s)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    t - s ≤
      (if t ≤ b then w t else w b + (t - b)) -
      (if s ≤ b then w s else w b + (s - b)) := by sorry
