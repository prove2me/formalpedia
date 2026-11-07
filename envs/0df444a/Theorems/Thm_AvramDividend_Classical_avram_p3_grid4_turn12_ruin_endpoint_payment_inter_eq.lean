-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn12_ruin_endpoint_payment_inter_eq
-- name    : AvramDividend.Classical.avram_p3_grid4_turn12_ruin_endpoint_payment_inter_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:44:19.63621+00:00
-- url     : https://prove2.me/theorems/1ace6ce0-3619-443f-ba1e-dff926cff08d
-- title:
--   Positive ruin clock excludes its endpoint from strict payment times and a stopped contact interval
-- statement:
--   When b is a positive real clock with ENNReal.ofReal b equal to the ruin threshold σ, b is excluded by paymentTimes σ: b is not zero and cannot be strictly before σ. Hence restricting the admissible payment-time set to (a,b] equals restricting it to (a,b). This authentic strict-ruin-endpoint identity removes an apparent atom from the last stopped cash cell when the contact clock equals ruin, without asserting anything about an independently surviving finite-horizon endpoint atom.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_turn12_ruin_endpoint_payment_inter_eq
    (σ : ℝ≥0∞) (b : ℝ) (hb : 0 < b)
    (hσ : ENNReal.ofReal b = σ) (a : ℝ) :
    paymentTimes σ ∩ Ioc a b = paymentTimes σ ∩ Ioo a b := by sorry
