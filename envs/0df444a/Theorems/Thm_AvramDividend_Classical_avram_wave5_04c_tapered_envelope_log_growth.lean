-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_envelope_log_growth
-- name    : AvramDividend.Classical.avram_wave5_04c_tapered_envelope_log_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:20:25.362198+00:00
-- url     : https://prove2.me/theorems/65274e5c-47e8-403d-b36c-338e4b576bac
-- title:
--   Tapered endpoint profile retains logarithmic BV growth envelope
-- statement:
--   If the tapered continuous profile vanishes below a and obeys a clamped profile envelope, the weighted taper retains the same logarithmic growth bound on all positive unit-interval arguments. This matches the Lipschitz payoff loss and controls the discarded negative-jump tail.
-- source:
--   Quantitative compact taper plus pointwise Lipschitz-logarithmic bound.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_tapered_envelope_log_growth
    (f : ℝ → ℝ) (G : C(unitInterval.Elem, ℝ))
    (a K : ℝ) (hK : 0 ≤ K)
    (hzero : ∀ t : unitInterval.Elem, (t : ℝ) ≤ a → G t = 0)
    (hbound : ∀ t : unitInterval.Elem,
      |G t| ≤ |f (max a (min (t : ℝ) 1))|)
    (hf : ∀ t : ℝ, a ≤ t → t ≤ 1 →
      |(1 - t) * f t| ≤ K * |Real.log t|) :
    ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |(1 - (t : ℝ)) * G t| ≤ K * |Real.log (t : ℝ)| := by sorry
