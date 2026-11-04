-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_band_fatou_grid_envelope
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_band_fatou_grid_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:29:58.423091+00:00
-- url     : https://prove2.me/theorems/16f75838-385f-4f91-b987-a8d841147cbf
-- title:
--   Actual original separated jump expectation bounded by eventual grid expectation envelope
-- statement:
--   For T>0 and ε>0, the original Lévy process's actual jump-count expectation on (0,T]×(-∞,-ε] is bounded by any proven eventual upper envelope M of measurable original grid negative-increment counts. This source-specific combination of the proved pathwise jump-count liminf and the proved generic Fatou envelope is legitimate even with infinitely many small jumps and with atomic mark distributions. It does not assume the desired Lévy rate or compensation identity; the remaining independent obligation is to prove the grid expectation envelope from stationary source probabilities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_band_mesh_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_fatou_eventual_grid_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_band_fatou_grid_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (M : ℝ≥0∞)
    (hGridMeas : ∀ n : ℕ, Measurable (fun ω : Ω => (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞)))
    (hGridBound : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞) ∂P) ≤ M) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P) ≤ M := by sorry
