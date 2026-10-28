-- Prove2me | Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_coeff_eq_moment
-- name    : D1Bound5.bennettPolynomialResidue_residual_coeff_eq_moment
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:57.827974+00:00
-- url     : https://prove2.me/theorems/91bb1b85-f238-4446-9bc2-bce098a89a9a
-- title:
--   Bennett Polynomial Residue residual coeff eq moment
-- statement:
--   Arbitrary coefficients of the genuine residual are local residue moments. This extends the low-degree cancellation identity to the high-degree tail.
-- source:
--   D1Bound5/BennettResidualEvaluation.lean, lines 97-131, SHA-256 d030bc1b298c007855437a873b058dcac35949cc3daa110cf555bdf87d4fd831. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5





section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]




theorem _root_.D1Bound5.bennettPolynomialResidue_residual_coeff_eq_moment
    {F : Type*} [Field F] [CharZero F]
    (a : I → F) (k : ℕ) (hk : 1 ≤ k) (ν : F) (i : I) (r : ℕ) :
    PowerSeries.coeff r
      (∑ j, (bennettPolynomialResidue univ a k ν i j : PowerSeries F) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) =
      Ring.choose ((k : F) + ν) r *
        ∑ j, bennettLocalResidue a
          (fun l => k + (if i = l then 1 else 0) - 1) (Polynomial.X ^ r) j := by sorry



end Nodes

end D1Bound5
end
