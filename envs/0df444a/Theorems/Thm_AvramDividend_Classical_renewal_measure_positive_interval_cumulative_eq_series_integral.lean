-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_measure_positive_interval_cumulative_eq_series_integral
-- name    : AvramDividend.Classical.renewal_measure_positive_interval_cumulative_eq_series_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:07:37.111261+00:00
-- url     : https://prove2.me/theorems/1e4faee9-6e41-4eef-96ef-60ba8aa9e76f
-- title:
--   Convolution renewal measure on (0,x] equals the real primitive of its power-series density
-- statement:
--   For nonnegative measurable convolution-power densities and matching measure powers starting with the zero Dirac atom, the renewal measure of a positive interval is exactly the real integral of the shifted density series. This combines the Proved atom-plus-real-density decomposition with the Proved nonnegative interval withDensity integral identity. The theorem is directly usable in the BV Esscher geometric-renewal scale identification needed for cstar_lt_top.
-- source:
--   Canonical renewal_measure_atom_plus_real_density and nonnegative_real_density_Ioc_toReal_eq_intervalIntegral.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_renewal_measure_atom_plus_real_density
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal

theorem AvramDividend.Classical.renewal_measure_positive_interval_cumulative_eq_series_integral
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x)))
    (x : ℝ) (hx : 0 ≤ x)
    (hint : IntervalIntegrable
      (fun y : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) :
    ((Measure.sum m) (Ioc (0 : ℝ) x)).toReal =
      ∫ y in (0 : ℝ)..x,
        (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y) := by sorry
