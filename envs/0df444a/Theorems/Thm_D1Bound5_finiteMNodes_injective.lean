-- Prove2me | Theorems.Thm_D1Bound5_finiteMNodes_injective
-- name    : D1Bound5.finiteMNodes_injective
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:27:01.636672+00:00
-- url     : https://prove2.me/theorems/18a83bfc-a777-4eee-a4e7-42b103574787
-- title:
--   Finite MNodes injective
-- statement:
--   Auxiliary result `finiteMNodes_injective` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteMBennettIdentity.lean, lines 106-127, SHA-256 291fd6ba981541548cef4bed5210986ea71cc1c1e28ff467e85be78d671f7779. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions

section
open Finset Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]













theorem _root_.D1Bound5.finiteMNodes_injective (a b s : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) :
    Function.Injective (finiteMNodes a b s) := by sorry



end D1Bound5
end
