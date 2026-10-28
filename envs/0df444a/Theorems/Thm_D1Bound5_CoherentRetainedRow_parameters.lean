-- Prove2me | Theorems.Thm_D1Bound5_CoherentRetainedRow_parameters
-- name    : D1Bound5.CoherentRetainedRow.parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:50.090666+00:00
-- url     : https://prove2.me/theorems/41eee5d9-786f-4ca6-9f3e-dba28cb002e5
-- title:
--   Coherent Retained Row — parameters
-- statement:
--   Auxiliary result `CoherentRetainedRow.parameters` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/CoherentRetainedMixedForms.lean, lines 14-29, SHA-256 eb96a42cf210b66dfcce899bd150fc1582a3f153a19beef7c93531438f527556. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentRetainedMixedForms_Definitions
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



theorem _root_.D1Bound5.CoherentRetainedRow.parameters {H lam U : ℝ}
    (hrow : CoherentRetainedRow H lam U) :
    1 < H ∧ H ≤ 48 ∧ U ≤ 179/10 ∧
      0 < coherentThreeLowerConstant H ∧ 0 < coherentThreeUpperConstant H ∧
      100*coherentThreeUpperConstant H/99 < lam ∧
      5 < 100/(201*coherentThreeUpperConstant H) ∧
      100/(199*coherentThreeLowerConstant H) < U := by sorry



end D1Bound5
end
