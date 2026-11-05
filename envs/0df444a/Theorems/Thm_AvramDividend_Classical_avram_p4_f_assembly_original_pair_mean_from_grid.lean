-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_mean_from_grid
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_pair_mean_from_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:48:25.183566+00:00
-- url     : https://prove2.me/theorems/df3aa315-5503-45e9-bdef-f53ebdc78aee
-- title:
--   Original chronological L1 pair mean assembled from finite-grid source expectations
-- statement:
--   On the same original X/P, finite-grid chronological pair count measurability, source pair-count a.e. measurability, and the actual original finite-grid mean limit imply the exact real chronological factorial pair L1 identity. Pointwise grid domination is discharged by a Proved original-source helper; Fatou squeeze and ENNReal-to-real L1 conversion are Proved. All three remaining source premises are explicit, for subsequent discharge before canonical P4-F.
-- source:
--   Accepted public b04c9f43 Fatou bridge, 903f2371 finite grid domination, 87898756 original source ENNReal-to-real L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_expectation_from_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_grid_pair_count_domination
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_ennreal_to_real_L1
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_pair_mean_from_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℝ≥0∞ := fun ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
    let r : ℝ :=
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    (∀ k, Measurable (A k)) →
    AEMeasurable K P →
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop (𝓝 (ENNReal.ofReal (r ^ 2 / 2))) →
    Integrable (fun ω =>
      2 * (((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ)) P ∧
    (∫ ω, 2 * (((F ω ×ˢ F ω).filter
      (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ) ∂P) = r ^ 2 := by sorry
