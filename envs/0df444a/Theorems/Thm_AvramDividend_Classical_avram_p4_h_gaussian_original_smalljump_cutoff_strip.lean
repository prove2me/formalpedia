-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:35:42.601003+00:00
-- url     : https://prove2.me/theorems/fe464249-d814-4237-883c-381d59c5f8ed
-- title:
--   Original intrinsic compensated small-jump cutoff difference equals its exact source marked-jump strip
-- statement:
--   On the same original probability space and original Lévy path, the difference between finite-band compensated small-jump integrals at cutoffs n and m is exactly the intrinsic marked jump integral over (-1/(n+1),-1/(m+1)] minus its actual source Lévy-measure compensator. No martingale, Poisson law, Gaussian construction or independent process is assumed.
-- source:
--   Deterministic set subtraction on actual X.X marked source measure; previously Proved original signed mark IntegrableOn on both source cutoff bands and source ν negative half-closed cutoff integrability. Mathlib.MeasureTheory.Integral.Bochner.Set theorem setIntegral_sdiff at pinned commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_halfclosed_band_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) (hnm : n ≤ m)
    (T : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let S : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω =
      (∫ p in (Ioc 0 T ×ˢ S), p.2 ∂NX) -
        (T : ℝ) * (∫ z in S, z ∂X.ν) := by sorry
