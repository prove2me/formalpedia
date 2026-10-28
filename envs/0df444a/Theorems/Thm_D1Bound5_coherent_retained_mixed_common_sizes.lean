-- Prove2me | Theorems.Thm_D1Bound5_coherent_retained_mixed_common_sizes
-- name    : D1Bound5.coherent_retained_mixed_common_sizes
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:32:26.693896+00:00
-- url     : https://prove2.me/theorems/fa23218b-ed83-4a16-bc1c-f67534f5ea20
-- title:
--   Coherent retained mixed common sizes
-- statement:
--   The mixed retained power gap with AT≥48 supplies the common large terminal hypotheses for the approximation constructions.
-- source:
--   D1Bound5/CoherentRetainedMixedFourSizes.lean, lines 82-101, SHA-256 bf8b694974926c3ebaa1cf7f2ccd931cddc284428c831b170580e4446c6fde48. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5






theorem _root_.D1Bound5.coherent_retained_mixed_common_sizes
    (A S T C : ℝ) (hA : 1 ≤ A) (hS3 : 3 ≤ S) (hST : S ≤ T)
    (hAT48 : 48 ≤ A*T) (hgap : A^2*T^5/S^2 < C) :
    1000 < C ∧ 200*S < C ∧ 4*T < C := by sorry

end D1Bound5
end
