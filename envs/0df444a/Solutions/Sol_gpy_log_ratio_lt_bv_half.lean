-- Prove2me | solution 1 for gpy_log_ratio_lt_bv_half
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T07:47:45.683979+00:00
-- url     : https://prove2.me/submissions/03e76031-fe9a-4eb5-94f8-16a7b215fe0a

/-
  Submission file for the Prove2Me problem `gpy_log_ratio_lt_bv_half` (PubAll batch, Oct 31, 2026).

  Self-contained: imports Mathlib only. Contains the verified bodies
  of the dependency chain plus the restated theorem, with top-level
  `theorem solution` in the problem's exact binder/statement form.
  No sorry tactic, no axioms beyond the standard ones, no platform imports.
-/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY

theorem log_ratio_lt_of_level {R Y' : ℕ} {θ η : ℝ}
    (hR : 2 ≤ R) (hY : 1 < Y')
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (θ - η)) :
    Real.log (R : ℝ) / Real.log (Y' : ℝ) < θ / 2 - η / 2 := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hYpos : (0 : ℝ) < (Y' : ℝ) := by exact_mod_cast (by omega : 0 < Y')
  have hlogY : (0 : ℝ) < Real.log (Y' : ℝ) := Real.log_pos (by exact_mod_cast hY)
  have h1 : Real.log ((R : ℝ) ^ 2) < Real.log ((Y' : ℝ) ^ (θ - η)) :=
    Real.log_lt_log (pow_pos hRpos 2) hlev
  rw [Real.log_pow, Real.log_rpow hYpos] at h1
  push_cast at h1
  rw [div_lt_iff₀ hlogY]
  linarith

/-- Level cap at BV level 1/2: under the platform BV record's
    constraint R² < Y'^{1/2-η}, the log ratio is below 1/4 - η/2.
    This is the whole level contribution the files can certify:
    it caps, but does not evaluate, the ratio's log factor. -/

theorem log_ratio_lt_bv_half {R Y' : ℕ} {η : ℝ}
    (hR : 2 ≤ R) (hY : 1 < Y')
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η)) :
    Real.log (R : ℝ) / Real.log (Y' : ℝ) < 1 / 4 - η / 2 := by
  have h := log_ratio_lt_of_level (θ := 1 / 2) hR hY hlev
  linarith

theorem log_ratio_lt_bv_half_restated_puball {R Y' : ℕ} {η : ℝ}
    (hR : 2 ≤ R) (hY : 1 < Y')
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η)) :
    Real.log (R : ℝ) / Real.log (Y' : ℝ) < 1 / 4 - η / 2 := by
  exact log_ratio_lt_bv_half hR hY hlev

end GPY

theorem solution {R Y' : ℕ} {η : ℝ}
    (hR : 2 ≤ R) (hY : 1 < Y')
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η)) :
    Real.log (R : ℝ) / Real.log (Y' : ℝ) < 1 / 4 - η / 2 := GPY.log_ratio_lt_bv_half_restated_puball hR hY hlev
