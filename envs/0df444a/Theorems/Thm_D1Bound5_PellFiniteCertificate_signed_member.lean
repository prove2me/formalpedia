-- Prove2me | Theorems.Thm_D1Bound5_PellFiniteCertificate_signed_member
-- name    : D1Bound5.PellFiniteCertificate.signed_member
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:49:03.099321+00:00
-- url     : https://prove2.me/theorems/9610d1a1-94fb-4e09-af69-b620527bb750
-- title:
--   Pell Finite Certificate — signed member
-- statement:
--   Auxiliary result `PellFiniteCertificate.signed_member` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PellFiniteCertificate.lean, lines 23-37, SHA-256 dcc2fd88b881b2c8eafcbde15c1cb33b51af6fe491a0856432d4dcd395c5e1ed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5



theorem _root_.D1Bound5.PellFiniteCertificate.signed_member {d X : ℤ}
    (C : PellFiniteCertificate d X) (hd : 7 ≤ d) (hX : 1 ≤ X)
    (u v z : ℤ) (hv : v ≠ 0) (heq : u^2-d*v^2=2)
    (hbound : u^2-1 ≤ X^2) (hz : z=d*v^2+1 ∨ z=-(d*v^2+1)) :
    PellSignedMember C.graph.magnitudes z := by sorry







end D1Bound5
end
