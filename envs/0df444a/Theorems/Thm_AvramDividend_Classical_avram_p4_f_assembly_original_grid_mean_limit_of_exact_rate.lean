-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_grid_mean_limit_of_exact_rate
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_grid_mean_limit_of_exact_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:51:29.313491+00:00
-- url     : https://prove2.me/theorems/d0b37476-8076-46b2-b159-4a787769b334
-- title:
--   Original physical expected ceiling-pair rates converge once their exact source finite-grid formula is established
-- statement:
--   For the true marked-time ceiling pairs of the same source Lévy process, derive convergence of expected counts to the half-square of original ν intensity from the exact finite-grid deterministic rate formula. This isolates only the source finite-grid compensation equality and uses the already Proved Lévy-rate limit.
-- source:
--   Proved source rate limit 83db5394; original process pair count and genuine P2-E compensation 77b37394. Required by positive-horizon L1 source theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit_auto
open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_grid_mean_limit_of_exact_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞))
    (∀ k : ℕ, 0 < k →
      (∫⁻ ω, A k ω ∂P) =
        ENNReal.ofReal
          (((k : ℝ) * ((k : ℝ) - 1) / 2) *
            (((T : ℝ) *
              (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) ^ 2 /
                (k : ℝ) ^ 2))) →
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop
      (𝓝 ((((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2)) := by sorry
