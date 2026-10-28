-- Prove2me | Theorems.Thm_D1Bound5_coherent_retained_mixed_coefficient_gt_one
-- name    : D1Bound5.coherent_retained_mixed_coefficient_gt_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:43:37.773149+00:00
-- url     : https://prove2.me/theorems/1400e7a1-c07f-4f41-a967-d04edad1bbe5
-- title:
--   Coherent retained mixed coefficient gt one
-- statement:
--   The retained coefficient remains greater than one when the first anchor has modulus only one, for either manuscript interpolation row.
-- source:
--   D1Bound5/CoherentRetainedMixedGap.lean, lines 11-44, SHA-256 a9ea1254a7294ce4c82a9ab4e53113abf8637681595eada76a4dfe19fad83d1c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open Finset
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.coherent_retained_mixed_coefficient_gt_one
    (A B R lam : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hR : 0 < R) (hR8 : R ≤ 8)
    (hlam : 0 < lam) (hlam10 : lam ≤ 1/10) :
    1 < (9999/10000 : ℝ)/lam^2 *
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by sorry



end D1Bound5
end
