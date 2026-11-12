-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger101_contact_cash_finite_algebra
-- name    : AvramDividend.Classical.avram_gledger101_contact_cash_finite_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:38:34.497667+00:00
-- url     : https://prove2.me/theorems/64373ad9-4d24-48a1-a14d-ed915a08559c
-- title:
--   Finite original cash/contact ledger closes after one crossing cell
-- statement:
--   A finite contact ledger has one final crossing cell and zero later cells. If strictly interior cash is offset by the preceding contact terms up to error R, the crossing plus terminal correction is nonpositive, the initial right-dividend atom offsets its cash, and all strict stopped cash lies within those pieces plus a final strip U, then the total positive residual is at most R+U. The argument is pure finite arithmetic, no new stochastic assumption or expected-reward inequality.
-- source:
--   Sound finite-sum algebra component for 16e988d7 original stopped dividend-contact correction: use Proved gledger97 crossing-cell index, gledger99 interior inequalities, gledger86 terminal payment cancellation, gledger95 cash partition. Remaining obligation is the exact original-path hypotheses needed to instantiate this abstract lemma; this child itself does not assert a stochastic result.

import Mathlib
open Finset
noncomputable section

theorem AvramDividend.Classical.avram_gledger101_contact_cash_finite_algebra
    (A : ℕ → ℝ) (N k : ℕ) (hk : k < N)
    (hafter : ∀ i : ℕ, k < i → A i = 0)
    (I U R F z cash0 term : ℝ)
    (hpre : (∑ i ∈ Finset.range k, A i) + I ≤ R)
    (hlast : A k + term ≤ 0)
    (hzero : z + cash0 ≤ 0)
    (hcash : F ≤ cash0 + I + U)
    (herr : 0 ≤ R + U) :
    max (z + (∑ i ∈ Finset.range N, A i) + term + F) 0 ≤ R + U := by sorry
