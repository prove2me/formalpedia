-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn12_surviving_horizon_payment_contact_split
-- name    : AvramDividend.Classical.avram_p3_grid4_turn12_surviving_horizon_payment_contact_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:45:59.387132+00:00
-- url     : https://prove2.me/theorems/5d1b83a9-812e-464d-b80a-a8f76bcce365
-- title:
--   Surviving finite-horizon stopped contact interval splits into strict cash and the endpoint atom
-- statement:
--   At a nonnegative deterministic horizon b strictly before ruin σ, the admissible payment-time set contains b. For a<b, the half-open contact interval (a,b] therefore splits exactly into the strict before-horizon payment interval (a,b) and the singleton {b}. This is the complementary surviving-horizon branch to the positive ruin-endpoint exclusion theorem; it preserves the otherwise missing dividend atom rather than silently discarding it.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_turn12_surviving_horizon_payment_contact_split
    (σ : ℝ≥0∞) (a b : ℝ) (hb : 0 ≤ b)
    (hpre : ENNReal.ofReal b < σ) (hab : a < b) :
    paymentTimes σ ∩ Ioc a b =
      (paymentTimes σ ∩ Ioo a b) ∪ {b} := by sorry
