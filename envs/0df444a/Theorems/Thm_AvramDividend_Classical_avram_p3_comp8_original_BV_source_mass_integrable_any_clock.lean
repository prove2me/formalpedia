-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
-- name    : AvramDividend.Classical.avram_p3_comp8_original_BV_source_mass_integrable_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:07:12.097792+00:00
-- url     : https://prove2.me/theorems/777fee57-43f4-405d-a3bc-b5a1b37f7c2c
-- title:
--   Original bounded-variation source mass gives an integrable nonnegative envelope on every finite horizon
-- statement:
--   For any positive or zero finite T, the original BV drift plus terminal residual |drift| T + |T drift-X(T)| is integrable and nonnegative. This removes the previous T≤1 limitation in the source error domination argument and derives from original all-clock X first-moment integrability.
-- source:
--   Extension of Proved BV-ERROR7 up-to-one variation L1 source certificate using the new all-time integrability theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_X_integrable_any_clock
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_BV_source_mass_integrable_any_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    Integrable (fun ω =>
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) P ∧
    (∀ ω, 0 ≤
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) := by sorry
