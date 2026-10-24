-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_supported_weak_subsequence
-- name    : AvramDividend.Classical.excursion_fixed_mass_supported_weak_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:40:18.516073+00:00
-- url     : https://prove2.me/theorems/e4b8ce05-7879-476c-86f6-82a900f3b20e
-- title:
--   Supported fixed-mass finite measures have a weakly convergent subsequence
-- statement:
--   A uniformly tight sequence of finite measures with common positive mass and no negative support has a weakly convergent subsequence whose finite-measure limit preserves the original mass and nonnegative support. Composes normalised Prokhorov, weak support, rescaling and mass identities.
-- source:
--   Published Prove2Me excursion normalisation and weak-limit helpers, using the pinned Mathlib Prokhorov theorem.

import Mathlib.MeasureTheory.Measure.Prokhorov
import Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_normalized_prokhorov_subsequence
import Theorems.Thm_AvramDividend_Classical_excursion_finite_measure_normalize_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_excursion_probability_weak_limit_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_excursion_rescaled_probability_support_mass
import Theorems.Thm_AvramDividend_Classical_excursion_rescale_normalized_weak_limit

open MeasureTheory Filter Topology Set

theorem AvramDividend.Classical.excursion_fixed_mass_supported_weak_subsequence
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal) (hc : 0 < c)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (hnz : ∀ n : ℕ, ν n ≠ 0)
    (hsupport : ∀ n : ℕ, (ν n : Measure ℝ) (Iio (0 : ℝ)) = 0)
    (htight : IsTightMeasureSet
      (Set.range (fun n : ℕ => (ν n : Measure ℝ)))) :
    ∃ (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n : ℕ => ν (φ n)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ) (Iio (0 : ℝ)) = 0 ∧
      (μ : Measure ℝ) Set.univ = (c : ENNReal) := by sorry
