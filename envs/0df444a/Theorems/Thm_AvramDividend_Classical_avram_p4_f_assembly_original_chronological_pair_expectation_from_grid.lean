-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_expectation_from_grid
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_expectation_from_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:52:05.193433+00:00
-- url     : https://prove2.me/theorems/b04c9f43-bfc0-4471-9ab5-04cb6f51e26c
-- title:
--   Original chronological negative-band pair expectation from all-finer grid convergence
-- statement:
--   Applies the Proved original marked-jump all-finer pair-set equality and independently Proved Fatou squeeze to the physical Lévy negative-band jump set, on the unchanged Ω/P/X. Each grid count is a genuine finset of observed jumps. Measurability, pointwise grid-to-chronological domination and expected finite-grid rate are named remaining source obligations, not smuggled into proof. No independent-process equality-in-law premise is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_all_finer_pair_set_equiv
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_eventually_exact_grid_fatou_squeeze
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_expectation_from_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : ℝ≥0∞) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℝ≥0∞ := fun ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
    (∀ k, Measurable (A k)) →
    (∀ k ω, A k ω ≤ K ω) →
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop (𝓝 r) →
    (∫⁻ ω, K ω ∂P) = r := by sorry
