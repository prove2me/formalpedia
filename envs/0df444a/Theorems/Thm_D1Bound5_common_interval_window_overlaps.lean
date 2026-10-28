-- Prove2me | Theorems.Thm_D1Bound5_common_interval_window_overlaps
-- name    : D1Bound5.common_interval_window_overlaps
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:10:19.339988+00:00
-- url     : https://prove2.me/theorems/5e69f577-68d1-47ed-874e-7ea05e7da787
-- title:
--   Common interval window overlaps
-- statement:
--   Parameterized endpoint calculation for both the five unbounded regions and the forty-one S≥15 first-pair regions. The relabeled N3 junction uses its pointwise coupled rho bound; K0 controls the stronger retained starting coefficient.
-- source:
--   D1Bound5/CommonIntervalOverlaps.lean, lines 5-363, SHA-256 740b9a120c34941ef978f437b53d0d137c1b026adbe49e502553a7784e62e51d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.common_interval_window_overlaps
    (A B S T C G rho K0 M2 Mn M3 M4 M5 Mbs R2 Rn R3 R4 R5 Rbs Rp : ℝ)
    (hA0 : 0 < A) (hB0 : 0 < B) (hS0 : 0 < S) (hBS : B ≤ S)
    (hG : 0 < G) (hrho : 0 < rho) (hK0 : 0 < K0)
    (hM2 : 0 < M2)
    (hMn : 0 < Mn)
    (hM3 : 0 < M3)
    (hM4 : 0 < M4)
    (hM5 : 0 < M5)
    (hMbs : 0 < Mbs)
    (hR2 : 0 < R2)
    (hRn : 0 < Rn)
    (hR3 : 0 < R3)
    (hR4 : 0 < R4)
    (hR5 : 0 < R5)
    (hRbs : 0 < Rbs)
    (hRp : 0 < Rp)
    (hT : 2*B*S < T) (hC : K0*A^2*T^5/S^2 < C)
    (hgap : G*(A^7*B^5*S^3) < C)
    (hgapbs : (rho*Rbs)*(A^7*B^5*S^3) < C)
    (hnum : CommonOverlapBounds A B S G rho K0 M2 Mn M3 M4 M5 Mbs R2 Rn R3 R4 R5 Rp) :
    (allLargeWindowQ A T C).1 < A^2*C^7/(S^2*T^4) ∧
    (commonWindowN2 A B C M2 R2).1 < (allLargeWindowQ A T C).2 ∧
    (commonWindowP A B S C Rp).1 < (commonWindowN2 A B C M2 R2).2 ∧
    (B^2 ≤ S → (commonWindowN3 A B C Mn Rn).1 < (commonWindowP A B S C Rp).2) ∧
    (commonWindowA3 A B C M3 R3).1 < (commonWindowP A B S C Rp).2 ∧
    (S ≤ B^2 → (allLargeWindowM A B S C).1 < (commonWindowA3 A B C M3 R3).2) ∧
    (commonWindowN3 A B C Mn Rn).1 < (allLargeWindowM A B S C).2 ∧
    (B^3 ≤ S → (commonWindowA4 A B C M4 R4).1 < (commonWindowN3 A B C Mn Rn).2) ∧
    (S ≤ B^3 → (commonWindowN3 B S C Mbs Rbs).1 < (commonWindowN3 A B C Mn Rn).2) ∧
    (commonWindowA4 A B C M4 R4).1 < (commonWindowN3 B S C Mbs Rbs).2 ∧
    ordinaryWindowLower B C 4 < (commonWindowA4 A B C M4 R4).2 ∧
    (commonWindowA5 A B C M5 R5).1 < ordinaryWindowUpper A B C 4 ∧
    ordinaryWindowLower B C 5 < (commonWindowA5 A B C M5 R5).2 ∧
    ordinaryWindowLower B C 6 < ordinaryWindowUpper A B C 5 ∧
    42*B^3*C < 2*A*C^2/(5*B) := by sorry

end D1Bound5
end
