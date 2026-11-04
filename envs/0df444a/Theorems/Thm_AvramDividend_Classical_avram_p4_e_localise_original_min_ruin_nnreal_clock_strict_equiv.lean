-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_min_ruin_nnreal_clock_strict_equiv
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_min_ruin_nnreal_clock_strict_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:50:39.664508+00:00
-- url     : https://prove2.me/theorems/742f4980-c19b-4853-a755-b3eae5a429f1
-- title:
--   Original min ruin NNReal stopping time and extended real strict time thresholds agree
-- statement:
--   For the actual exact P4-F stopping clock τ=ENNReal.toNNReal(min(ruinTime,n)), prove the strict physical-time threshold t<τ is equivalent to (t:ENNReal)<min(ruinTime,n) pathwise for every sample and every t, including a zero or infinite ruin time. Finiteness comes only from n, preserving all t=0, ruin, and horizon conventions. No stochastic hypothesis is needed.
-- source:
--   P4-F original source exact stopped clock; Mathlib ENNReal.coe_toNNReal and strict finite coe order.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original finite clipped clock agrees with the strict extended-real min threshold. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_min_ruin_nnreal_clock_strict_equiv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω (t : ℝ≥0),
      t < τ ω ↔ (t : ℝ≥0∞) <
        min (ruinTime X x D ω) (n : ℝ≥0∞) := by sorry
