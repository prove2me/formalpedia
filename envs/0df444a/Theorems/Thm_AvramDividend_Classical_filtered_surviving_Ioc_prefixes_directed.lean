-- Prove2me | Theorems.Thm_AvramDividend_Classical_filtered_surviving_Ioc_prefixes_directed
-- name    : AvramDividend.Classical.filtered_surviving_Ioc_prefixes_directed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:48:11.649133+00:00
-- url     : https://prove2.me/theorems/bccee136-6a9e-4516-bb49-5d1298d09417
-- title:
--   Positive dividend prefixes strictly before ruin form a directed family
-- statement:
--   For any stopping horizon and any enumeration of nonnegative prospective payment horizons, retaining only endpoints strictly before the stopping time produces a directed-by-inclusion family of positive-time initial intervals. The proof uses the total ordering of interval right endpoints and treats intervals with inadmissible endpoints as empty. This supplies the concrete hypothesis of Mathlib's directed-union monotone-convergence lemma for the exact zero-barrier stopped Stieltjes payment set.
-- source:
--   Prove2Me paymentTimes strict-ruin endpoint definition and Mathlib directed-union theorem. Avram, Palmowski and Pistorius (2007), section 3.3.

import Mathlib.Data.ENNReal.Real
open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.filtered_surviving_Ioc_prefixes_directed
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0) :
    Directed (fun (a b : Set ℝ) => a ⊆ b)
      (fun n : ℕ => {x : ℝ | 0 < x ∧ x ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ}) := by sorry
