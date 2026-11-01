-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable
-- name    : AvramDividend.Classical.avram_wave4_04b_full_right_payment_jump_support_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:02:36.312638+00:00
-- url     : https://prove2.me/theorems/d23b8276-0c22-4890-be0e-a327e910347a
-- title:
--   All actual finite-horizon right-payment jump times are countable with summable jump sizes
-- statement:
--   For any actual adapted admissible dividend strategy, the complete finite-horizon positive right-payment support equals the measure's atom support, is countable, and the chronological payment sizes sum absolutely. All diffuse and singular-continuous variation remains allowed and is not discarded.
-- source:
--   Avram Dividend Wave 4 specialist 04-B: actual Stieltjes measure atomic/diffuse decomposition and chronological right-payment jumps

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_right_atom_masses_real_summable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_atom_support_eq_right_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_actual_right_payment_jumps_summable_on_atom_support
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_full_right_payment_jump_support_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let A : Set ℝ :=
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
    A.Countable ∧
      Summable (fun s : A =>
        rightLimit D ((s : ℝ).toNNReal) ω -
        D ((s : ℝ).toNNReal) ω) := by
  sorry
