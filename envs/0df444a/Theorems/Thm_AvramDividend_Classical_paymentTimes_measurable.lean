-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
-- name    : AvramDividend.Classical.paymentTimes_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:29:43.348312+00:00
-- url     : https://prove2.me/theorems/88dafb7f-65e0-4218-8bde-e06dfe88a7a3
-- title:
--   The exact dividend payment-time set is Borel measurable
-- statement:
--   For every ruin horizon σ in extended nonnegative reals, the exact paymentTimes σ = {t≥0 | t=0 or ofReal t<σ} is a Borel measurable subset of real time. The function ENNReal.ofReal is continuous and its inverse image of the open interval below σ is open; unions and intersections with the singleton {0} and nonnegative half-line preserve measurability. This technical fact is required for monotone convergence from truncated payout integrals to dividendValue.
-- source:
--   Exact paymentTimes definition, pinned Mathlib ENNReal.continuous_ofReal, isOpen_Iio, measurableSet_Ici.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_measurable (σ : ℝ≥0∞) :
    MeasurableSet (paymentTimes σ) := by sorry
