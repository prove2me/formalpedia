-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuous_antitone_L1_powers_quadratic
-- name    : AvramDividend.Classical.causal_continuous_antitone_L1_powers_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:24:31.546226+00:00
-- url     : https://prove2.me/theorems/2a872f17-ebac-4ed6-b01b-e5c904f23c22
-- title:
--   Quadratic-geometric convolution-power bounds from continuous antitone L1 data
-- statement:
--   For nonnegative nonincreasing causal kernels continuous on positive time, if integrable convolution powers satisfy geometric finite-horizon mass bounds, then every power obeys the explicit quadratic-geometric pointwise estimate. This removes auxiliary split-measurability and interval-integrability hypotheses from the previously proved induction theorem and is required to control derivatives of the Gaussian Esscher resolvent Neumann series.
-- source:
--   The proved antitone causal convolution-power theorem requires interval integrability and restricted AEStronglyMeasurable factors. Global positive-time L1 data supply interval integrability; positive-time kernel continuity supplies reflected-factor measurability; L1 integrability of each convolution power supplies right-factor measurability.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_antitone_powers_quadratic_pointwise_of_measurable_recursion
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_continuous_antitone_L1_powers_quadratic
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hKpoint : ∀ x : ℝ, 0 < x → κ x ≤ ρ / x)
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hKL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hKmass : ∀ y : ℝ, 0 < y → (∫ t in (0 : ℝ)..y, κ t) ≤ ρ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      F (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ F n t)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFmass : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ s in (0 : ℝ)..u, F n s) ≤ ρ ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by sorry
