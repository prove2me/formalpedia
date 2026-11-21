-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_true_all_right_payment_atoms_signed_tsum_nonpos
-- name    : AvramDividend.Classical.avram_ga_true_all_right_payment_atoms_signed_tsum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:30:17.661863+00:00
-- url     : https://prove2.me/theorems/6e14b907-e02b-461e-afc5-0f9376a2e3e9
-- title:
--   Entire countable original right-dividend Itô correction is nonpositive under slope-one secants
-- statement:
--   For an arbitrary indexed (potentially countably infinite) family of original chronological right-payment jumps J_i≥0, discount weights E_i≥0, and prepayment reserve Y_i, the signed Itô–Stieltjes correction sum of E_i*(V(Y_i−J_i)−V(Y_i)+J_i) is nonpositive whenever the source candidate V has global slope-one secants and the signed series is summable. This is the full right-atom sign input for the stopped smooth ledger and includes an atom at time zero when the index set includes it.
-- source:
--   Global finite-cap auxiliary secant from new proved f0c6c841 plus nonnegative discounted payment atoms and order of summable real series. Exact Stieltjes atomic/diffuse support source d19177af and corrected chronological jump identity source 14ce41c4. A true source-specific finite-variation summability transfer remains separate.

import Mathlib
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_true_all_right_payment_atoms_signed_tsum_nonpos
    {ι : Type*} (V : ℝ → ℝ) (Y J E : ι → ℝ)
    (hSec : ∀ a b : ℝ, a ≤ b → b - a ≤ V b - V a)
    (hJ : ∀ i, 0 ≤ J i) (hE : ∀ i, 0 ≤ E i)
    (hSummable : Summable
      (fun i => E i * (V (Y i - J i) - V (Y i) + J i))) :
    (∑' i, E i * (V (Y i - J i) - V (Y i) + J i)) ≤ 0 := by sorry
