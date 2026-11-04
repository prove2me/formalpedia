-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_real_mesh_mass_bound
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_real_mesh_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:41:03.534881+00:00
-- url     : https://prove2.me/theorems/ac34ac77-4b20-4621-858c-bafa32b4ca35
-- title:
--   Eventually bounded original negative one-time grid probability mass along genuine positive uniform real mesh
-- statement:
--   For the original spectrally negative Levy process and every positive finite horizon T and negative separation ε, there exists a finite positive constant C such that eventually the sum of (n+1) genuine source one-time negative-increment event probabilities at the real mesh T/(n+1), evaluated at its nonnegative-time embedding, is at most ENNReal.ofReal(C*T). It specialises the already-Proved original uniform small-time negative-tail bound along the already-Proved positive-grid filter limit. The statement does not identify jump rates and preserves the original source probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_uniform_negative_grid_probability_mass
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_uniform_mesh_tendsto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_real_mesh_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (((n + 1 : ℕ) : ℝ≥0∞) *
        P {ω : Ω | X.X (Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω ≤ -ε}) ≤
      ENNReal.ofReal (C * (T : ℝ)) := by sorry
