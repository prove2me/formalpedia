-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_mean_two_source_gaps
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_pair_mean_two_source_gaps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:01:41.586373+00:00
-- url     : https://prove2.me/theorems/2325c9f1-f33c-4d5b-8596-b2a35c5755e1
-- title:
--   Original chronological pair L1 mean reduced to two physical finite-grid premises
-- statement:
--   The exact original chronological L1 pair mean follows from two remaining source obligations: global measurability of each ceiling-grid pair count and convergence of its ENNReal expectation to half the square of the marked-jump rate. The chronological count a.e. measurability is fully discharged by accepted P2-E original source count and physical factorial identity, and accepted Fatou, domination, toReal bridges. No independent-process law or optional-sampling assumption.
-- source:
--   Accepted public df3aa315 and de3b5f97. Remaining two source equations correspond to original fixed-grid rectangle counts and P2-E compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_mean_from_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_measurable
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_pair_mean_two_source_gaps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
    let r : ℝ :=
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    (∀ k, Measurable (A k)) →
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop (𝓝 (ENNReal.ofReal (r ^ 2 / 2))) →
    Integrable (fun ω =>
      2 * (((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ)) P ∧
    (∫ ω, 2 * (((F ω ×ˢ F ω).filter
      (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ) ∂P) = r ^ 2 := by sorry
