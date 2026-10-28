-- Prove2me | Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio
-- name    : D1Bound5.bennett_exists_integral_root_ratio
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:55.382173+00:00
-- url     : https://prove2.me/theorems/1c63b454-9d24-424d-a95b-b6648d6a8898
-- title:
--   Bennett exists integral root ratio
-- statement:
--   The source-ring witness is a sign of the existing product of integral roots. It is chosen once, independently of the later matrix row.
-- source:
--   D1Bound5/BennettRootApproximation.lean, lines 50-84, SHA-256 ca1061aebc87736a011fd6e5cb0011ac939b7397422bdbe21a20c1861b490805. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.bennett_exists_integral_root_ratio
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a c d z r v : R) (θ : ℂ)
    (ha : f a ≠ 0) (hc : f c ≠ 0) (hz : f z ≠ 0) (hθ0 : θ ≠ 0)
    (hr : r ^ 2 = a * c + 1) (hv : v ^ 2 = a * d + 1)
    (hzsq : z ^ 2 = c * d + 1) (hθ : θ ^ 2 = 1 + 1 / (f a * f c)) :
    ∃ s : R, (s = r * v ∨ s = -(r * v)) ∧
      0 ≤ ((f s / (f a * f z)) / θ).re ∧
      ‖θ - f s / (f a * f z)‖ ≤
        ‖θ‖ * ‖f c - f a‖ / (‖f a‖ * ‖f z‖ ^ 2) := by sorry





end D1Bound5
end
