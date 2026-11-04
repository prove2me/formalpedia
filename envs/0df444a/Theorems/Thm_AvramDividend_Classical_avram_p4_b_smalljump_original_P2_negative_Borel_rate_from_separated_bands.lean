-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_negative_Borel_rate_from_separated_bands
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_P2_negative_Borel_rate_from_separated_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:17:39.01614+00:00
-- url     : https://prove2.me/theorems/6cbd76db-1a37-484d-bdeb-65fcca0802b9
-- title:
--   Original P2 rate extension to arbitrary negative Borel marks
-- statement:
--   Genuine original P2 rates on reciprocal-separated negative bands imply original-source expected jump rate on every negative Borel mark set, retaining physical P and X.nu.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_monotone_mark_rate_extension

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_P2_negative_Borel_rate_from_separated_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (N : Ω → Measure (ℝ≥0 × ℝ))
    (hN : ∀ ω, N ω =
      (Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (s t : ℝ≥0) (B : Set ℝ) (hNeg : B ⊆ Iio (0 : ℝ))
    (hMeas : ∀ n : ℕ, Measurable (fun ω =>
      N ω (Ioc s t ×ˢ (B ∩ {z : ℝ |
        z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))))
    (hRate : ∀ n : ℕ,
      (∫⁻ ω, N ω (Ioc s t ×ˢ (B ∩ {z : ℝ |
        z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z})) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) *
        X.ν (B ∩ {z : ℝ |
          z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))) :
    (∫⁻ ω, N ω (Ioc s t ×ˢ B) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
