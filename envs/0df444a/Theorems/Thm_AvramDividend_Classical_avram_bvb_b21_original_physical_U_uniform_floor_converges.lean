-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_physical_U_uniform_floor_converges
-- name    : AvramDividend.Classical.avram_bvb_b21_original_physical_U_uniform_floor_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:12:41.646736+00:00
-- url     : https://prove2.me/theorems/1cbc1f52-9e98-4a32-9fa8-27a2ba39f5fa
-- title:
--   Original physical prepayment reserve converges along genuine uniform left-grid samples
-- statement:
--   On a source-exact zero-jump original path, the actual reserve before right dividend payments at the canonical uniform floor-grid points approaches the original reserve left limit at any strictly positive time. Uses the original X, Ω, D, admissibility, and drift source, and approaches from times no later than t. This is a missing pointwise kernel-convergence input in the selected 7ccc2a1a compensator route.
-- source:
--   Original physical pointwise reserve sampler for 7ccc2a1a K-minus-A compensator convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_physical_U_uniform_floor_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (T : ℝ) (hT : 0 < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    Tendsto (fun n => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (s n))
      atTop (𝓝 (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t)) := by sorry
