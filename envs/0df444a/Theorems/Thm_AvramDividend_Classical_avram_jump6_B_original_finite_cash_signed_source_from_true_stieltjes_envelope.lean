-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
-- name    : AvramDividend.Classical.avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:57:35.497201+00:00
-- url     : https://prove2.me/theorems/d293d5a8-5e38-4a74-9b6c-6ef4a6246717
-- title:
--   True discounted finite Stieltjes cash upper bound converts to signed source-residual budget
-- statement:
--   Finish the exact payment accounting needed for the original strict stopped-clock dividend source: a pathwise ENNReal bound for original inclusive cash by nonnegative initial rightpayment atom plus true physical-grid discounted potential drops plus finite mesh error implies the signed real cash-and-potential residual is no greater than that mesh error. Uses publicly Proved finite original ENNReal discounted sum conversion and Cash+finite-error real bridge. This is the algebraic bridge for the original C=top stopped payment branch; all original physical source terms remain the quantities to be supplied.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_closed_cash_ennreal_budget_toReal_signed_error
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_ennreal_discounted_cash_finite_grid_sum_toReal
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
    {ι : Type*} (S : Finset ι) (D0 Wx Wpost : ℝ)
    (E H : ι → ℝ) (Cash Error : ℝ≥0∞)
    (hD0 : 0 ≤ D0)
    (hE : ∀ i ∈ S, 0 ≤ E i)
    (hH : ∀ i ∈ S, 0 ≤ H i)
    (hInitial : D0 + Wpost - Wx ≤ 0)
    (hErrorFinite : Error ≠ ⊤)
    (hCash : Cash ≤ ENNReal.ofReal D0 +
      (∑ i ∈ S, ENNReal.ofReal (E i) * ENNReal.ofReal (H i)) + Error) :
    Cash.toReal + (Wpost - Wx) - (∑ i ∈ S, E i * H i) ≤ Error.toReal := by sorry
