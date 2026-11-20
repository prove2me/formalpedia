-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_anyactivity_natural_negative_cutoff_compensated_cell_L1_centered
-- name    : AvramDividend.Classical.avram_jump6_B_actual_anyactivity_natural_negative_cutoff_compensated_cell_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:09:53.435167+00:00
-- url     : https://prove2.me/theorems/26e170cc-45f5-4b02-8b04-688263c60c2e
-- title:
--   Original infinite-activity natural negative cutoffs: exact marked count compensator L1 and zero mean
-- statement:
--   For any spectrally negative Levy process with possibly infinite total negative-jump intensity, every cutoff n yields an original marked jump count over (s,t] with marks ≤-1/(n+1), centred by its true local Levy rate. The real centred source count is integrable with exact expectation zero. Local finite intensity follows from the Levy integrability field; the compensator rate follows from the original source count Campbell identity. All time and mark arguments remain those of the same X and ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_centered_jump_mean_zero
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_actual_anyactivity_natural_negative_cutoff_compensated_cell_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
      (∫ ω, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 := by sorry
