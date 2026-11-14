-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b102_original_all_spatial_stop_rows_exact_physical_jump_finsets_ae
-- name    : AvramDividend.Classical.avram_b102_original_all_spatial_stop_rows_exact_physical_jump_finsets_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:53:08.869884+00:00
-- url     : https://prove2.me/theorems/96da04d2-2d0b-46ec-817b-672d0c03abf4
-- title:
--   Exact finite original physical Lévy jump-time witness Finset at all rows of the random spatial stopping-clock family
-- statement:
--   From the proved original finite-negative-activity same-source theorem, obtain one P-conull event on which all bounded physical intervals contain finitely many genuine nonzero left-limit source jump times. For any arbitrary sequence of actual random sample-path stopping clocks κ(k,ω), each row k has a finite exact witness set of actual jump times in (0,κ(k,ω)], with membership if and only if the genuine original Lévy source jump occurs then. The construction is simultaneous for all k on one conull event, and is the exact input to the marked-cell cardinal injection proof and genuine stopped physical source decomposition.
-- source:
--   Proved avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae and Mathlib Set.Finite.toFinset.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every genuine original random clipping clock has a finite exact source-jump witness set on one conull event. -/

theorem AvramDividend.Classical.avram_b102_original_all_spatial_stop_rows_exact_physical_jump_finsets_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      ∃ F : Finset ℝ≥0,
        ∀ u : ℝ≥0, u ∈ F ↔
          0 < u ∧ u ≤ κ k ω ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by sorry
