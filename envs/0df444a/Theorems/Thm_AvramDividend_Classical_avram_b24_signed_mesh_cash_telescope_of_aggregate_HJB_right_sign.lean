-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_signed_mesh_cash_telescope_of_aggregate_HJB_right_sign
-- name    : AvramDividend.Classical.avram_b24_signed_mesh_cash_telescope_of_aggregate_HJB_right_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:13:11.466383+00:00
-- url     : https://prove2.me/theorems/cb669445-13cb-4bd1-b7e9-a478d62fecf5
-- title:
--   Exact finite stopped cash telescope from aggregate nonpositive HJB and payment drift
-- statement:
--   Summing finite original stopped cash ledger cell inequalities bounds the terminal discounted reward plus initial and all interval cash by initial value plus Gaussian and compensated jump gains and the mesh error, provided the aggregate signed HJB/right-dividend drift is nonpositive. Each individual drift contribution may have either sign. This retains the time-zero cash atom and the exact last stopped cell.
-- source:
--   Proved b21 signed finite mesh cash telescope and original b24 combined discounted HJB/right cash signed finite sum theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_signed_mesh_cash_telescope_of_aggregate_HJB_right_sign
    (N : ℕ) (w0 cash0 : ℝ)
    (V cash gaussian jump drift error : ℕ → ℝ)
    (hInitial : V 0 + cash0 ≤ w0)
    (hCell : ∀ i, i < N →
      V (i + 1) + cash i ≤
        V i + gaussian i + jump i + drift i + error i)
    (hTotal : (∑ i ∈ Finset.range N, drift i) ≤ 0) :
    V N + cash0 + (∑ i ∈ Finset.range N, cash i) ≤
      w0 + (∑ i ∈ Finset.range N, gaussian i) +
        (∑ i ∈ Finset.range N, jump i) +
        (∑ i ∈ Finset.range N, error i) := by sorry
