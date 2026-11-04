-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_random_weight_short_strip_L1_vanishes
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_random_weight_short_strip_L1_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:06:11.043959+00:00
-- url     : https://prove2.me/theorems/6833f1d5-7bc0-4e8e-a970-ff62bb3df648
-- title:
--   Original Lévy bounded random marked-weight shrinking-strip L1 limit
-- statement:
--   For original intrinsic Lévy marked jumps and genuinely random nonnegative weights H_n bounded uniformly by a finite constant, the event-restricted weighted jump count in a shrinking source time strip converges to zero in L1. Conditional only on the true finite physical Lévy mark intensity and unconditional source rate of P2.
-- source:
--   Accepted original source random-weight bound d34f39c4 and Mathlib ENNReal finite multiplication continuity and order squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_bounded_random_weight_short_strip

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_random_weight_short_strip_L1_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (r : ℕ → ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (A : Set Ω)
    (H : ℕ → Ω → ℝ≥0∞) (K : ℝ≥0∞)
    (hBound : ∀ n ω, H n ω ≤ K)
    (hFinite : X.ν B ≠ ⊤) (hKFinite : K ≠ ⊤)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hRate : ∀ n, (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s (r n) ×ˢ B) ∂P) =
       ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Tendsto (fun n => (∫⁻ ω in A, H n ω *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s (r n) ×ˢ B) ∂P)) atTop (𝓝 0) := by sorry
