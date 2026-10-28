-- Prove2me | Theorems.Thm_D1Bound5_bennettPoleSeries_mul
-- name    : D1Bound5.bennettPoleSeries_mul
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:21:46.148406+00:00
-- url     : https://prove2.me/theorems/72ebcf33-52ea-4ad4-95ce-9d9d880b2ea2
-- title:
--   Bennett Pole Series mul
-- statement:
--   The explicit binomial coefficients really invert the reciprocal pole factor, rather than merely satisfying a guessed recurrence.
-- source:
--   D1Bound5/BennettPoleSeries.lean, lines 28-48, SHA-256 d467fe1ce7d532a4e4fe7ebbe139b749331fe498c06b5ac2897ed0a4d7fa6354. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]








theorem _root_.D1Bound5.bennettPoleSeries_mul (d : F) (hd : d ≠ 0) (k : ℕ) :
    (PowerSeries.C d + PowerSeries.X : PowerSeries F) ^ k * bennettPoleSeries d k = 1 := by sorry

end D1Bound5
end
