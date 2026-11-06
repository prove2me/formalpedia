-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_fixed_horizon_exact_centered_L2_variance
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_band_fixed_horizon_exact_centered_L2_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:19:42.592693+00:00
-- url     : https://prove2.me/theorems/1279879b-317a-4167-b701-c1974ed76439
-- title:
--   Actual original negative-band Poisson count has exact compensated fixed-horizon L2 variance
-- statement:
--   For the actual original spectrally negative Lévy process, the fixed-horizon count of all jumps below −1/(n+1) minus its Lévy intensity r=Tν((−∞,−1/(n+1)]) is square-integrable and has exact second-moment r. This has no extra count integrability, first-moment, factorial-moment, Poisson-law or independent-copy assumptions. It closes all source premises of the existing physical chronological-pair centered-count L² identity using already Proved original physical factorial and mean laws.
-- source:
--   Combines Proved P4-F original chronological pair mean d938e9a5, original cutoff marked count L1 3d8bb7f8, P2 original separated negative ν finiteness and exact zero-origin rate, P2 finite-ν physical Bochner mean 14c106db, and source L2 pair algebra 7e452475. This is exact actual-process negative-band centred isometry for deterministic time horizons, upstream of physical-grid small-jump energy.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_mean_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_centered_count_l2_pair_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_negative_band_fixed_horizon_exact_centered_L2_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (J ω - r) ^ 2) P ∧
      (∫ ω, (J ω - r) ^ 2 ∂P) = r := by sorry
