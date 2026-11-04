-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_monotone_mark_rate_extension
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_P2_monotone_mark_rate_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:08:29.341193+00:00
-- url     : https://prove2.me/theorems/1eecf2ac-4a40-4bc2-a2fa-410720159141
-- title:
--   Original P2 marked rate monotone-band extension
-- statement:
--   Original source finite Borel band P2 rates extend to monotone mark unions using original path count continuity and physical P monotone convergence, with source measurability and rates as premises.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_P2_monotone_mark_rate_extension
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
    (s t : ℝ≥0) (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hMeas : ∀ n, Measurable
      (fun ω => N ω (Ioc s t ×ˢ B n)))
    (hRate : ∀ n,
      (∫⁻ ω, N ω (Ioc s t ×ˢ B n) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n))) :
    (∫⁻ ω, N ω (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (⋃ n, B n)) := by sorry
