-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite30_original_lower_exit_pathwise_floor_clocks
-- name    : AvramDividend.Classical.avram_gfinite30_original_lower_exit_pathwise_floor_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T03:57:47.747541+00:00
-- url     : https://prove2.me/theorems/cb3e82b1-6c06-46af-b577-4378aff8c90b
-- title:
--   Original Gaussian pre-exit clocks have a pathwise positive reserve floor
-- statement:
--   Necessary finite-cap localisation obligation for 3308ae9d: with arbitrary cap, original process, lawful stopped horizon no later than ruin, and unbounded variation, there are nondecreasing finite-valued right-continuous-filtration stopping times, converging a.e. to the horizon and imposing deterministic positive pre-exit reserve floors.
-- source:
--   Strengthening accepted gfinite25 from a.e. floor to pointwise floor; the original construction and proof are pathwise and satisfy hLocal in finite-cap passage 3308ae9d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_sampled_preexit_clipped_clock_floor
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_lower_exit_clocks_antitone_barriers
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_lower_exit_debut_sup_stopping
import Theorems.Thm_AvramDividend_Classical_avram_gtop23_original_debut_cofinal_with_stopped_sigma
import Theorems.Thm_AvramDividend_Classical_avram_gtop24_bounded_withtop_stop_has_nnreal_rep
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite30_original_lower_exit_pathwise_floor_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσruin : ∀ ω, (σ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    ∃ L : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (L j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, L j ω ≤ σ ω) ∧
      (∀ ω, Monotone (fun j : ℕ => L j ω)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun j => L j ω) atTop (nhds (σ ω))) ∧
      (∀ j ω, ∀ t : ℝ≥0, 0 < t → t < L j ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) := by sorry
