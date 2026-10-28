-- Prove2me | Theorems.Thm_D1Bound5_ordinaryLog10_lt_of_pow_lt
-- name    : D1Bound5.ordinaryLog10_lt_of_pow_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:37.168553+00:00
-- url     : https://prove2.me/theorems/53b558db-a493-407e-bb50-42e0f70deeb1
-- title:
--   Ordinary Log10 lt of pow lt
-- statement:
--   Exact integer-power comparisons certify all decimal logarithm parameters; no decimal approximation or external numerical oracle is used.
-- source:
--   D1Bound5/OrdinaryLog10.lean, lines 34-40, SHA-256 09aeaea7ebd8948074c88ecfb8ed793209871b3b024d7443a02f1048da4ea91c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5


















theorem _root_.D1Bound5.ordinaryLog10_lt_of_pow_lt (x : ℝ) (m n : ℕ)
    (hx : 0 < x) (hpow : x^n < (10 : ℝ)^m) :
    (n : ℝ)*ordinaryLog10 x < m := by sorry





end D1Bound5
end
