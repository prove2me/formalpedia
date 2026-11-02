-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile_quantitative
-- name    : AvramDividend.Classical.avram_wave5_04c_tapered_compact_profile_quantitative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:16:53.588812+00:00
-- url     : https://prove2.me/theorems/a6569a18-7098-4a0a-a9a5-00e6a1386cb9
-- title:
--   Quantitative compact taper preserving a pointwise envelope on the unit interval
-- statement:
--   A continuous function on [a,1] admits a continuous taper that is zero below a, agrees above b, and is absolutely dominated by the original profile evaluated at the interval clamp. The third bound controls finite-band Lévy jump cutoff transition errors.
-- source:
--   Source-faithful strengthening of previously Proved compact taper theorem.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_tapered_compact_profile_quantitative (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hb : b ≤ 1)
    (hf : ContinuousOn f (Set.Icc a 1)) :
    ∃ G : C(unitInterval.Elem, ℝ),
      (∀ t : unitInterval.Elem, (t : ℝ) ≤ a → G t = 0) ∧
      (∀ t : unitInterval.Elem, b ≤ (t : ℝ) → G t = f (t : ℝ)) ∧
      (∀ t : unitInterval.Elem,
        |G t| ≤ |f (max a (min (t : ℝ) 1))|) := by sorry
