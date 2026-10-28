-- Prove2me | Theorems.Thm_D1Bound5_bennettPoleSeries_coeff
-- name    : D1Bound5.bennettPoleSeries_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:44.221209+00:00
-- url     : https://prove2.me/theorems/25dad53a-1f3c-4035-abe5-d87836eee532
-- title:
--   Bennett Pole Series coeff
-- statement:
--   Exact Taylor coefficients of the local reciprocal pole factor.
-- source:
--   D1Bound5/BennettPoleSeries.lean, lines 14-20, SHA-256 d467fe1ce7d532a4e4fe7ebbe139b749331fe498c06b5ac2897ed0a4d7fa6354. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]




theorem _root_.D1Bound5.bennettPoleSeries_coeff (d : F) (k h : ℕ) :
    PowerSeries.coeff h (bennettPoleSeries d k) =
      Ring.choose (-(k : F)) h * (d⁻¹) ^ (k + h) := by sorry





end D1Bound5
end
