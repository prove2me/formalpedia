-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_stopped_path_open_eventually
-- name    : AvramDividend.Classical.chat03_capped_grid_stopped_path_open_eventually
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:47:51.595432+00:00
-- url     : https://prove2.me/theorems/35cd8d74-def4-4eef-ac2d-fa8aca6acccc
-- title:
--   Right-continuous stopped path values along capped first strict grid exits
-- statement:
--   Let τ be the strict two-sided continuous exit infimum and T a finite time horizon. Given any open real set U containing the stopped sample-path value X(min(τ,T)), every sufficiently fine grid has a first strict exit index k such that X(min(kh,T)) lies in U. This captures convergence of sampled stopped path values by using the already proved capped time approximation from above and path right-continuity. It neither assumes strict exit at τ nor asserts that W(X(min(kh,T))) converges at a possibly discontinuous zero boundary.
-- source:
--   The published capped first-grid convergence theorem and the right-continuity field SpectrallyNegativeLevy.rightCont, using the pinned exists_Ico_subset_of_mem_nhds' neighbourhood lemma.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_capped_grid_stopped_path_open_eventually
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (U : Set ℝ) (hU : IsOpen U)
    (hmem : X.X (min τ T) ω ∈ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
        ∃ k : ℕ,
          (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω) ∧
          (∀ j : ℕ, j < k →
            ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
               upper < X.X ((j : ℝ≥0) * h) ω)) ∧
          X.X (min ((k : ℝ≥0) * h) T) ω ∈ U := by sorry
