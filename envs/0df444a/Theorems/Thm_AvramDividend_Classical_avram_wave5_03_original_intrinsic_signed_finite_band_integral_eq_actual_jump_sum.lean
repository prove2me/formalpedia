-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
-- name    : AvramDividend.Classical.avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:47:55.16566+00:00
-- url     : https://prove2.me/theorems/b881e8e7-8c17-4354-822b-33855df6c8f1
-- title:
--   Original signed intrinsic Lévy integral on a finite negative mark band equals the exact source jump-time sum
-- statement:
--   At a fixed sample of the original spectrally negative Levy path, for a measurable negative mark band with a finite enumeration S of the actual source jumps during (s,t], and an explicitly integrable real signed marked kernel f, the Bochner real integral of the band-and-horizon masked kernel against the genuine intrinsic jump measure equals the actual Finset sum f(u,ΔX_u). It follows from the separately Proved original signed marked integral-to-tsum identity, with source mark negativity proving that every band mark is a nonzero genuine positive-time source jump, and finite support converting the unrestricted tsum exactly to S. This is an authentic bridge between finite-band original controlled Ito–Meyer corrections and the actual intrinsic jump measure; it does not assume compensation or independence.
-- source:
--   Original source jump graph and time/mark counting measure, Proved source signed real identity c1360947, BV ef7e6c20 and corrected UBV 429e17ca. Depends on actual finite enumeration only, no artificial source process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (B : Set ℝ) (hBmeas : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
      s < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B)
    (f : (ℝ≥0 × ℝ) → ℝ) (hf : Measurable f)
    (hfin : Integrable
      (fun p : ℝ≥0 × ℝ =>
        if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then f p else 0)
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    (∫ p, (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then f p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S, f (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
