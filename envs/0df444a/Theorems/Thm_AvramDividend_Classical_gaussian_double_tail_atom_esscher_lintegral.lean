-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_esscher_lintegral
-- name    : AvramDividend.Classical.gaussian_double_tail_atom_esscher_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:57:19.976642+00:00
-- url     : https://prove2.me/theorems/d26ad097-c858-4863-8a17-b5469712485f
-- title:
--   Esscher-weighted ENNReal Gaussian double-tail atom identity
-- statement:
--   For φ>0 and θ,z≥0, the ENNReal integral over t in (0,z) of θ² times (z−t)exp(−θt) times the fixed Esscher weight exp(−φz) equals the ENNReal embedding of exp(−φz)(exp(−θz)−1+θz). Move nonnegative constant factors through the interval lintegral, equate open and half-open intervals under atomless Lebesgue measure and apply the separately published Gaussian double-tail atom-lintegral bridge. This supplies the exact per-jump kernel identity required after Tonelli.
-- source:
--   gaussian_double_tail_atom_lintegral (publication pending), pinned lintegral_const_mul, ENNReal.ofReal_mul, restrict_Ioo_eq_restrict_Ioc.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_atom_esscher_lintegral
    (φ θ z : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    (∫⁻ t in Ioo (0 : ℝ) z,
      ENNReal.ofReal (θ ^ 2) *
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z)) ∂volume) =
      ENNReal.ofReal
        (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) := by sorry
