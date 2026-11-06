-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:28:51.178684+00:00
-- url     : https://prove2.me/theorems/2aaf4594-3924-41fe-95ed-e82fdbbcb294
-- title:
--   Actual original full negative-cutoff bounded predictable compensated cell L² martingale step and zero mean
-- statement:
--   An actual full negative cutoff physical jump-count compensated increment on (s,s+T], multiplied by any bounded rightCont-s predictable coefficient H, is L², has zero conditional expectation on the same right-continuous physical filtration at s, and has zero ordinary terminal mean. No synthetic Poisson marks and no assumed moment/uniform integrability; all assertions are finite-cutoff.
-- source:
--   Combine exact shifted source count conditional mean and variance with automatic weighted L² and ambient source count measurability. Pull H out of rightCont conditional expectation, then integrate the latter to prove zero mean.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let Z : Ω → ℝ := fun ω => H ω * ((N ω).toReal - r)
    MemLp Z 2 P ∧
    (P[Z | 𝓕.rightCont s] =ᵐ[P] (fun _ => 0)) ∧
    (∫ ω, Z ω ∂P) = 0 := by sorry
