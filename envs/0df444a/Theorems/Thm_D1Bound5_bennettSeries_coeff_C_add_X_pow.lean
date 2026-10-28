-- Prove2me | Theorems.Thm_D1Bound5_bennettSeries_coeff_C_add_X_pow
-- name    : D1Bound5.bennettSeries_coeff_C_add_X_pow
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:44.363866+00:00
-- url     : https://prove2.me/theorems/f1ddb363-c405-4f0a-97b9-42351d3c5cdf
-- title:
--   Bennett Series coeff C add X pow
-- statement:
--   Polynomial binomial coefficients, viewed in formal power series.
-- source:
--   D1Bound5/BennettBinomialTransfer.lean, lines 10-18, SHA-256 7c8a669a4f1cc287328c81f5b671e332dd23a6d5cc77c366017077852274896c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]


theorem _root_.D1Bound5.bennettSeries_coeff_C_add_X_pow (a : F) (r h : ℕ) :
    PowerSeries.coeff h ((PowerSeries.C a + PowerSeries.X : PowerSeries F) ^ r) =
      a ^ (r - h) * (r.choose h : F) := by sorry



end D1Bound5
end
