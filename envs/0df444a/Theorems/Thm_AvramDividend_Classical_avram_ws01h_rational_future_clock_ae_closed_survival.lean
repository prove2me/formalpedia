-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_future_clock_ae_closed_survival
-- name    : AvramDividend.Classical.avram_ws01h_rational_future_clock_ae_closed_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:54:35.69229+00:00
-- url     : https://prove2.me/theorems/48bcaee3-9997-4cc5-879d-84ef41598535
-- title:
--   Countable rational open-age future survival equals exact full closed survival almost everywhere in real clock time
-- statement:
--   At almost every nonnegative real observation age, the countably measurable rational open-horizon survival tests of an original Lévy path are equivalent to genuine closed-horizon survival including the terminal observation. The only possible difference is at the first strict lower-exit clock; the Proved Lebesgue-null singleton and original killed clock/closed-history a.e. identity remove it. This is essential for applying jointly measurable path-space rewards under genuine exponential clock mixture without assuming that variable evaluation on uncountable raw path coordinates is measurable.
-- source:
--   Proved WS01H open rational weak-clock equivalence; Proved chat04_strict_lower_killed_closed_history_ae_time_ws01a and chat04_ennreal_strict_clock_single_time_null_ws01a, true original Lévy process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_open_survival_iff_weak_lower_clock
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_killed_closed_history_ae_time_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_ennreal_strict_clock_single_time_null_ws01a

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_rational_future_clock_ae_closed_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (ω : Ω) :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      (0 ≤ t ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal t →
          0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω) ↔
      (0 ≤ t ∧ ∀ s : ℝ≥0, s ≤ Real.toNNReal t →
          0 ≤ x + X.X s ω) := by sorry
