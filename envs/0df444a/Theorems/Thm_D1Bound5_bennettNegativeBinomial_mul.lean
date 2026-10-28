-- Prove2me | Theorems.Thm_D1Bound5_bennettNegativeBinomial_mul
-- name    : D1Bound5.bennettNegativeBinomial_mul
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:00.233897+00:00
-- url     : https://prove2.me/theorems/637e7425-6180-4907-a9da-8c98d5bbab4a
-- title:
--   Bennett Negative Binomial mul
-- statement:
--   The negative-integer binomial series is the formal inverse of `(1+X)^k`.
-- source:
--   D1Bound5/BennettPoleSeries.lean, lines 22-26, SHA-256 d467fe1ce7d532a4e4fe7ebbe139b749331fe498c06b5ac2897ed0a4d7fa6354. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]






theorem _root_.D1Bound5.bennettNegativeBinomial_mul (k : ℕ) :
    (1 + PowerSeries.X : PowerSeries F) ^ k * binomialSeries F (-(k : F)) = 1 := by sorry



end D1Bound5
end
