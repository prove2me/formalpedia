-- Prove2me | Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio_bound_finite
-- name    : D1Bound5.bennett_exists_integral_root_ratio_bound_finite
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:14.412517+00:00
-- url     : https://prove2.me/theorems/f56ba3df-f23b-4e1e-8a96-fb92bb1b16cb
-- title:
--   Bennett exists integral root ratio bound finite
-- statement:
--   The finite-family root comparison retains one sign of the original integral product. The larger anchor separation improves the factor from 3/2 to the manuscript's101/100.
-- source:
--   D1Bound5/FiniteRootApproximation.lean, lines 5-47, SHA-256 3eb0625b1bc5b24d5bf964a4f1ffefb0c9955b498e80c90017d816a9b67d0609. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.bennett_exists_integral_root_ratio_bound_finite
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a c d z r v : R)
    (ha : f a ≠ 0) (hc : f c ≠ 0) (hz : f z ≠ 0)
    (hr : r^2 = a*c+1) (hv : v^2 = a*d+1) (hzsq : z^2 = c*d+1)
    (hAC : 1000 ≤ ‖f a‖*‖f c‖) (hC : 200*‖f a‖ ≤ ‖f c‖) :
    ∃ s : R, (s = r*v ∨ s = -(r*v)) ∧
      ‖(1+1/(f a*f c))^(1/2 : ℂ)-f s/(f a*f z)‖ <
        (101/100 : ℝ)*‖f c‖/(‖f a‖*‖f z‖^2) := by sorry

end D1Bound5
end
