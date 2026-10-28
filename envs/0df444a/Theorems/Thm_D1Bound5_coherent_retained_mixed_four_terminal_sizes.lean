-- Prove2me | Theorems.Thm_D1Bound5_coherent_retained_mixed_four_terminal_sizes
-- name    : D1Bound5.coherent_retained_mixed_four_terminal_sizes
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:13.518005+00:00
-- url     : https://prove2.me/theorems/047e94be-f7da-4f67-a5d6-6d897d2f1b78
-- title:
--   Coherent retained mixed four terminal sizes
-- statement:
--   The repeated retained power gap supplies the direct-four separation and excludes the zero-form upper window.
-- source:
--   D1Bound5/CoherentRetainedMixedFourSizes.lean, lines 38-80, SHA-256 bf8b694974926c3ebaa1cf7f2ccd931cddc284428c831b170580e4446c6fde48. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.coherent_retained_mixed_four_terminal_sizes
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hST : S ≤ T) (hSC : S ≤ C)
    (hC1000 : 1000 < C) (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D) :
    1000*C < D ∧ 17*A*B*S*T*C^3 < D := by sorry



end D1Bound5
end
