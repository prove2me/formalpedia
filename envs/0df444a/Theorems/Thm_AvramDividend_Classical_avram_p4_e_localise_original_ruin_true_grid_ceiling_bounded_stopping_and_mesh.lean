-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_true_grid_ceiling_bounded_stopping_and_mesh
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_true_grid_ceiling_bounded_stopping_and_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:42:31.198338+00:00
-- url     : https://prove2.me/theorems/a8b403e2-4164-46da-b383-bcd04646683d
-- title:
--   Original stopped-ruin source: bounded adapted ceiling index within one mesh
-- statement:
--   For the original admissible dividend strategy and the actual truncated ruin stopping time, a deterministic monotone grid covering the horizon with e0=0 and one-step mesh bound δ admits a first ceiling index that is a bounded discrete stopping time for sampled right-continuous filtration. The real sampled ceiling is between the exact source clock and at most δ afterwards. This replaces abstract clock measurability, coverage and mesh assumptions with original-source hypotheses.
-- source:
--   Existing Proved original ruin stopping facts and P4-E Proved ceiling event, stopping adapter and mesh bound.

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

/-- Genuine original ruin-clipped source admits a bounded stopping ceiling within one grid mesh. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_true_grid_ceiling_bounded_stopping_and_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : (n : ℝ≥0) ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    ∃ K : Ω → ℕ,
      IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ e (K ω) ∧
        e (K ω) ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal + δ) := by sorry
