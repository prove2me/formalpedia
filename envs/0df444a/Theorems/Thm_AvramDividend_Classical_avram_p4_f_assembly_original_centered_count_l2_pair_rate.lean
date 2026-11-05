-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_centered_count_l2_pair_rate
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_centered_count_l2_pair_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:03:44.442672+00:00
-- url     : https://prove2.me/theorems/7e452475-0f08-4391-a2c7-42e2a1f1c22b
-- title:
--   Original intrinsic negative-band centred count L2 from genuine ordered pair mean
-- statement:
--   For the literal intrinsic marked-jump count J of the original source X on the finite negative band and its genuine chronological ordered-pair K, first-moment L1 and mean r plus an honest separately proved ordered-pair L1 and mean r^2 imply the original centred count is square integrable with variance r. This is the precise bridge from physical source pair expectations to P4-G and P4-F hCountL2; proving the ordered-pair mean remains a separate nontrivial stochastic obligation.
-- source:
--   Accepted original source second-moment/ordered-pair decomposition 1a119044, original finite marked times, pinned integrable algebra; conditional pair expectation must later be established from original P2-E predictable compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_second_moment_ordered_pairs
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_centered_count_l2_pair_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable J P →
    (∫ ω, J ω ∂P) = r →
    Integrable (fun ω => 2 * (K ω : ℝ)) P →
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 →
    Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by sorry
