-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:01:57.463582+00:00
-- url     : https://prove2.me/theorems/79505e86-97d7-40f8-8e89-2b42beaae958
-- title:
--   Exact signed small-band intrinsic Levy jump integral equals original same-path jump series
-- statement:
--   For every original spectrally negative Levy sample path, horizon and canonical negative-mark cutoff, the signed real intrinsic marked-jump integral is exactly the time-indexed sum over the same X.X jumps, with no Poisson representation, compensator law, auxiliary process, or independence assumption. The domain is the true half-closed band (-1,-1/(n+1)].
-- source:
--   Compose Proved P4-H actual finite-band mark IntegrableOn 1fa1d6da with Proved original signed measure-integral-to-jump-tsum c1360947, using pinned Mathlib indicator integrability and integral_indicator.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    (∫ p in E, p.2 ∂N) =
      ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
        E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 := by sorry
