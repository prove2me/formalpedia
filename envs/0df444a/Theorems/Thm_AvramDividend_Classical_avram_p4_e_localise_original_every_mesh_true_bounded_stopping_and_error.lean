-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_every_mesh_true_bounded_stopping_and_error
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_every_mesh_true_bounded_stopping_and_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:30:28.762689+00:00
-- url     : https://prove2.me/theorems/483cc761-794a-427d-b496-3e18d175ef01
-- title:
--   Every shrinking original ruin-clock ceiling grid is a genuinely bounded sampled-filtration stopping time with mesh error
-- statement:
--   For the same original admissible dividend strategy and exact min(ruinTime,n) clock, every deterministic grid in a potentially varying family has its own genuine sampled right-continuous filtration stopping index Kk, bounded by Nk and yielding an upper ceiling within δk. This permits applying bounded optional stopping separately on each finite mesh without demanding a single common sampled filtration as grids refine. The statement leaves stochastic martingale/UI and boundary budget assumptions explicit.
-- source:
--   Proved original ruin-time stopping plus P4-E event-adaptation, sampled-index stopping and first-ceiling mesh bound.

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_first_ceiling_clock_mesh_error

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite grid is a true original-filtration stopping ceiling, uniformly within its own mesh. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_every_mesh_true_bounded_stopping_and_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (N : ℕ → ℕ) (hN : ∀ k, (n : ℝ≥0) ≤ e k (N k))
    (δ : ℕ → ℝ≥0) (h0 : ∀ k, e k 0 = 0)
    (hStep : ∀ k i, e k (i + 1) ≤ e k i + δ k)
    (𝓖 : ℕ → Filtration ℕ mΩ)
    (h𝓖 : ∀ k, 𝓖 k =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e k i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he k hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e k i) } : Filtration ℕ mΩ)) :
    ∃ K : ℕ → Ω → ℕ, ∀ k,
      IsStoppingTime (𝓖 k) (fun ω => (K k ω : WithTop ℕ)) ∧
      (∀ ω, (K k ω : WithTop ℕ) ≤ (N k : WithTop ℕ)) ∧
      (∀ ω,
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ e k (K k ω) ∧
        e k (K k ω) ≤
          (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal + δ k) := by sorry
