-- Prove2me | Theorems.Thm_D1Bound5_finitePRowForm_eq_root_sum
-- name    : D1Bound5.finitePRowForm_eq_root_sum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:16.09616+00:00
-- url     : https://prove2.me/theorems/6984b552-ae5e-4e08-9fa3-e5fbb287aabe
-- title:
--   Finite PRow Form eq root sum
-- statement:
--   Auxiliary result `finitePRowForm_eq_root_sum` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePRowBound.lean, lines 10-15, SHA-256 5b4887df5ceda709ccd98651207d9d1529e4eb3c0cfdfb72d875c244851c6512. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Definitions.Def_D1Bound5_FinitePIntegralRows_Definitions
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions

section
namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem _root_.D1Bound5.finitePRowForm_eq_root_sum (a b s c z rA rB rS : ℂ) (i : Fin 4) :
    finitePRowForm a b s c z rA rB rS i =
      finitePDividedMatrix a b s c i 0*z+
        ∑ j : Fin 3, finitePRootColumn a b s c i j*![rA,rB,rS] j := by sorry



end D1Bound5
end
