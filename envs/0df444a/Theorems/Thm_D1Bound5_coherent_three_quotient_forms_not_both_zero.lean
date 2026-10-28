-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_quotient_forms_not_both_zero
-- name    : D1Bound5.coherent_three_quotient_forms_not_both_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:18.890499+00:00
-- url     : https://prove2.me/theorems/4b5477b9-0d70-43d9-b36d-929b46fade95
-- title:
--   Coherent three quotient forms not both zero
-- statement:
--   Simultaneous nonvanishing for the actual two coherent quotient forms. The chosen analytic roots supply all square identities; the remaining hypotheses are precisely distinctness, ordering and size.
-- source:
--   D1Bound5/CoherentThreeNonvanishing.lean, lines 171-206, SHA-256 20f76d470fd8a77be69b6cbe7c960d5062bc8bb2410754eb1f27bcf0090be809. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_CoherentThreeNonvanishing_Definitions

section
open Finset

namespace D1Bound5














theorem _root_.D1Bound5.coherent_three_quotient_forms_not_both_zero
    (a : Fin 4 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (heta : eta^2 = p*q)
    (hA : 1 ≤ ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hBS : ‖a 1‖ ≤ ‖a 2‖) (hST : ‖a 2‖ ≤ ‖a 3‖)
    (hTP : ‖a 3‖ ≤ ‖p‖) (hPQ : ‖p‖ ≤ ‖q‖)
    (hsize : 32*‖a 1‖*‖a 2‖*‖a 3‖/‖a 0‖^3 ≤ ‖p‖^2) :
    coherentQuotientForm (coherentTriple012 a)
      (coherentVandermonde3 (coherentTriple012 a)) p q eta ≠ 0 ∨
    coherentQuotientForm (coherentTriple013 a)
      (coherentVandermonde3 (coherentTriple013 a)) p q eta ≠ 0 := by sorry

end D1Bound5
end
