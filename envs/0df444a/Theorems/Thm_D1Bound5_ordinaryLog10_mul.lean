-- Prove2me | Theorems.Thm_D1Bound5_ordinaryLog10_mul
-- name    : D1Bound5.ordinaryLog10_mul
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:45:05.725833+00:00
-- url     : https://prove2.me/theorems/7b940733-fb0c-4c55-bafa-f5d8c4c42067
-- title:
--   Ordinary Log10 mul
-- statement:
--   Auxiliary result `ordinaryLog10_mul` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OrdinaryLog10.lean, lines 10-13, SHA-256 09aeaea7ebd8948074c88ecfb8ed793209871b3b024d7443a02f1048da4ea91c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5





theorem _root_.D1Bound5.ordinaryLog10_mul (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordinaryLog10 (x*y) = ordinaryLog10 x+ordinaryLog10 y := by sorry

















end D1Bound5
end
