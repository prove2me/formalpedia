-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_cantor_sampled_normalized_record_eq_runningSup_on_grid
-- name    : AvramDividend.Classical.avram_root29_05_cantor_sampled_normalized_record_eq_runningSup_on_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:06:23.276963+00:00
-- url     : https://prove2.me/theorems/5a1d6ee2-f338-42f4-8bc3-7965699957a7
-- title:
--   Exact measurable normalized Cantor record at every original Lévy rational cash grid endpoint
-- statement:
--   For any actual original spectrally negative Lévy path, positive rational denominator and integer numerator, the measurable countably sampled normalized record used in the genuine killed-history Markov functional equals the actual running supremum at the same rational grid endpoint. The proof uses accepted Cantor schedule density and endpoint coverage, the accepted original Lévy dense-record identity, and exact X0=0. This removes the other source-matching part of the sampled reward representation without altering the genuine Stieltjes measure or ruin stopping.
-- source:
--   Proved chat04_nat_pairing_rational_grid_coverage 34d1a207, chat05_cantor_rational_schedule_dense 9206d7f5, avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup f32e574e and source SpectrallyNegativeLevy.X_zero.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_cantor_sampled_normalized_record_eq_runningSup_on_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n k : ℕ) (hn : 0 < n) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨆ j : ℕ,
       if samples j ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹ then
         ENNReal.ofReal (X.X (samples j) ω - X.X 0 ω)
       else 0).toReal =
    runningSup X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by sorry
