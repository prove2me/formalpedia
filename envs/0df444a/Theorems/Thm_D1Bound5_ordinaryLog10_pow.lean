-- Prove2me | Theorems.Thm_D1Bound5_ordinaryLog10_pow
-- name    : D1Bound5.ordinaryLog10_pow
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:59:32.245434+00:00
-- url     : https://prove2.me/theorems/ee5fc8c6-ef5d-4f79-a29e-31b0cc5ba434
-- title:
--   Ordinary Log10 pow
-- statement:
--   Auxiliary result `ordinaryLog10_pow` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OrdinaryLog10.lean, lines 15-18, SHA-256 09aeaea7ebd8948074c88ecfb8ed793209871b3b024d7443a02f1048da4ea91c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5







theorem _root_.D1Bound5.ordinaryLog10_pow (x : ℝ) (n : ℕ) :
    ordinaryLog10 (x^n) = n*ordinaryLog10 x := by sorry















end D1Bound5
end
