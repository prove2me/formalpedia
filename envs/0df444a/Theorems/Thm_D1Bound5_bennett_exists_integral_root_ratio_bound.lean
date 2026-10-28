-- Prove2me | Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio_bound
-- name    : D1Bound5.bennett_exists_integral_root_ratio_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:07.095009+00:00
-- url     : https://prove2.me/theorems/0fa1fa35-48a9-4a86-b2a8-1240b4ad720d
-- title:
--   Bennett exists integral root ratio bound
-- statement:
--   A uniform root-transfer estimate with the same final constant3 as the manuscript. The stronger entry bounds permit the simple factor3/2 here, avoiding a monotonicity argument for the auxiliary function e(X).
-- source:
--   D1Bound5/BennettRootApproximation.lean, lines 86-117, SHA-256 ca1061aebc87736a011fd6e5cb0011ac939b7397422bdbe21a20c1861b490805. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.bennett_exists_integral_root_ratio_bound
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a c d z r v : R)
    (ha : f a ≠ 0) (hc : f c ≠ 0) (hz : f z ≠ 0)
    (hr : r ^ 2 = a * c + 1) (hv : v ^ 2 = a * d + 1)
    (hzsq : z ^ 2 = c * d + 1)
    (hAC : 1000 ≤ ‖f a‖ * ‖f c‖) (hC : 4 * ‖f a‖ ≤ ‖f c‖) :
    ∃ s : R, (s = r * v ∨ s = -(r * v)) ∧
      ‖(1 + 1 / (f a * f c)) ^ (1 / 2 : ℂ) - f s / (f a * f z)‖ <
        (3 / 2 : ℝ) * ‖f c‖ / (‖f a‖ * ‖f z‖ ^ 2) := by sorry



end D1Bound5
end
