-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_negative_Borel_mark_simple_mean_of_separated_P2
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_negative_Borel_mark_simple_mean_of_separated_P2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:29:05.466806+00:00
-- url     : https://prove2.me/theorems/d464cd08-0848-4955-abe8-3e6649d539ef
-- title:
--   Original negative Borel mark-simple mean from separated P2 rates
-- statement:
--   For the original intrinsic jump measure, separated negative Borel mark-rate identities imply the expected finite nonnegative mark-simple integral matches the original Lévy intensity.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_negative_Borel_rate_from_separated_bands
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_mark_simple_raw_integral_mean

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_negative_Borel_mark_simple_mean_of_separated_P2
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hNeg : ∀ i ∈ S, B i ⊆ Iio (0 : ℝ))
    (c : ι → ℝ≥0∞)
    (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i))
    (hCutMeas : ∀ i ∈ S, ∀ n : ℕ,
      Measurable (fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B i ∩ {z : ℝ |
            z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))))
    (hCutRate : ∀ i ∈ S, ∀ n : ℕ,
      (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B i ∩ {z : ℝ |
            z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z})) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i ∩ {z : ℝ |
            z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc s t ×ˢ B i).indicator (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑ i ∈ S, c i * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
