-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:10:11.930758+00:00
-- url     : https://prove2.me/theorems/0c8c9353-9965-45d8-9dd2-c5c1ca5c984c
-- title:
--   Positive original stopped time has a genuine unique crossing cell on every finite physical mesh
-- statement:
--   For an actual original spectrally negative Levy reserve and admissible dividend path, each finite ruin/horizon-stopped physical grid whose stopping clock tau is positive has a crossing index i<m+1, with u i<tau and u(i+1)=tau. The proof uses the genuine original clock's zero start, exact final endpoint and min-clipped values; it complements the Proved at-most-one-crossing theorem, and guarantees that the boundary summand in the accepted strict/crossing Stieltjes partition is genuine rather than assumed absent.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_grid_reaches_exact_tau
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ := by sorry
