-- Prove2me | Theorems.Thm_D1Bound5_coherent_retained_mixed_size_parameters
-- name    : D1Bound5.coherent_retained_mixed_size_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:06.529929+00:00
-- url     : https://prove2.me/theorems/72b7f772-53c9-4e44-aae4-c1d4e39963c7
-- title:
--   Coherent retained mixed size parameters
-- statement:
--   The preliminary retained size bounds when only the first anchor may have modulus below three. The first L2 gap is needed to obtain the input for the second L2 gap.
-- source:
--   D1Bound5/CoherentRetainedMixedSizes.lean, lines 5-70, SHA-256 4052953496a6dda73eb03810524dfb628d86696644b05029e09eaad381eb4055. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5


theorem _root_.D1Bound5.coherent_retained_mixed_size_parameters
    (A B S T C : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hBS : B ≤ S)
    (hAT32 : 32 ≤ A*T) (hT : 2*A*B*S < T) (hC : 3*A*B*S*T < C) :
    5*S ≤ T ∧ 5*A*B*T ≤ C ∧ 32 ≤ A*T ∧ 4*T ≤ C ∧ 10000 < T*C ∧
      (A^2*T^3 < (10001/10000 : ℝ)*C → 5*B*S*T ≤ C) ∧
      (B^2*T^3 < (10001/10000 : ℝ)*C → (179/10 : ℝ)*A*B*S*T^2 < C) := by sorry

end D1Bound5
end
