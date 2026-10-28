-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_null_no_jump_grid
-- name    : AvramDividend.Classical.ae_early_downward_jumps_of_null_no_jump_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:59:29.674989+00:00
-- url     : https://prove2.me/theorems/76ccf378-0f33-404c-a0d4-912b94c5f620
-- title:
--   Countable null no-jump intervals imply almost-sure arbitrarily early downward jumps
-- statement:
--   For a spectrally negative Lévy sample path, suppose each interval in a countable family shrinking to zero has a null exceptional event on which no genuine negative jump occurs. Almost surely, every interval has a negative jump. Given an arbitrary positive horizon, a smaller grid horizon supplies the required jump. This is the countable-almost-everywhere bridge to the previously Proved zero-barrier reflected-supremum identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), zero-barrier jump activity discussion after (3.13), https://arxiv.org/pdf/math/0702893. Mathlib MeasureTheory.OuterMeasure.AE.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Data.NNReal.Basic

open MeasureTheory Set Filter
open scoped NNReal

namespace AvramDividend.Classical

/-- A countable null no-jump grid gives almost-sure downward jumps arbitrarily near zero. -/
theorem ae_early_downward_jumps_of_null_no_jump_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, δ n < ε)
    (hnull : ∀ n : ℕ,
      P {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ n ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l} = 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l := by sorry

end AvramDividend.Classical
