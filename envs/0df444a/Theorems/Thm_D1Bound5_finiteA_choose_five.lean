-- Prove2me | Theorems.Thm_D1Bound5_finiteA_choose_five
-- name    : D1Bound5.finiteA_choose_five
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:05.375489+00:00
-- url     : https://prove2.me/theorems/d75237d2-9c25-4c65-a102-a20e80323494
-- title:
--   Finite A choose five
-- statement:
--   Auxiliary result `finiteA_choose_five` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteChooseFive.lean, lines 25-29, SHA-256 bde24ed91fa3925db41d2480e279480d17f11937e1a240043403eb90798427c3. Project: https://github.com/tomislav-math/d1-bound5-lean

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







theorem _root_.D1Bound5.finiteA_choose_five (r : F) : Ring.choose r 5 = r*(r-1)*(r-2)*(r-3)*(r-4)/120 := by sorry

end D1Bound5
end
