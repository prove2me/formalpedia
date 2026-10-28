-- Prove2me | Theorems.Thm_D1Bound5_finiteA_choose_two
-- name    : D1Bound5.finiteA_choose_two
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:13.511447+00:00
-- url     : https://prove2.me/theorems/01ad6b33-2de1-4ae2-bdc1-11dc15433c22
-- title:
--   Finite A choose two
-- statement:
--   Auxiliary result `finiteA_choose_two` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteChooseFive.lean, lines 7-11, SHA-256 bde24ed91fa3925db41d2480e279480d17f11937e1a240043403eb90798427c3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5
variable {F : Type*} [Field F] [CharZero F]

theorem _root_.D1Bound5.finiteA_choose_two (r : F) : Ring.choose r 2 = r*(r-1)/2 := by sorry







end D1Bound5
end
