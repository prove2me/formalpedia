-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_cash_positive_excess_norm_le_original_two_noise_envelopes
-- name    : AvramDividend.Classical.avram_b24_original_cash_positive_excess_norm_le_original_two_noise_envelopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:23:20.134602+00:00
-- url     : https://prove2.me/theorems/0149c9ff-77d5-4ab3-9d80-413398241f97
-- title:
--   Cash positive deficit norm bounded by original cash norm, baseline and two genuine noise envelopes
-- statement:
--   For real discounted original stopped cash F, initial value w, and genuine original Gaussian and compensated marked grid gains G,J dominated in norm by nonnegative real envelopes BG,BJ, the norm of the positive cash deficit max(F-w-G-J,0) is bounded by the sum of |F|, |w|, BG and BJ. This pointwise real inequality supplies the exact integrable source envelope for dominated convergence in the actual B24 positive-clock cash error transfer; no probabilistic additional assumption, fake noise or cash simplification.
-- source:
--   Real norm and triangle inequalities, genuine source gain envelope premises.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_cash_positive_excess_norm_le_original_two_noise_envelopes
    (F w G J BG BJ : ℝ)
    (hG : ‖G‖ ≤ BG) (hJ : ‖J‖ ≤ BJ) :
    ‖max (F - w - G - J) 0‖ ≤ ‖F‖ + ‖w‖ + BG + BJ := by sorry
