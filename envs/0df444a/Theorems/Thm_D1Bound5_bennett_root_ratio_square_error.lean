-- Prove2me | Theorems.Thm_D1Bound5_bennett_root_ratio_square_error
-- name    : D1Bound5.bennett_root_ratio_square_error
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:45:24.394021+00:00
-- url     : https://prove2.me/theorems/61a79cf6-baf0-4fa7-b983-7107facf3542
-- title:
--   Bennett root ratio square error
-- statement:
--   Exact algebraic error for the two products of tuple roots.
-- source:
--   D1Bound5/BennettRootApproximation.lean, lines 38-48, SHA-256 ca1061aebc87736a011fd6e5cb0011ac939b7397422bdbe21a20c1861b490805. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.bennett_root_ratio_square_error
    (a c d z r v θ : ℂ) (ha : a ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (hr : r ^ 2 = a * c + 1) (hv : v ^ 2 = a * d + 1)
    (hzsq : z ^ 2 = c * d + 1) (hθ : θ ^ 2 = 1 + 1 / (a * c)) :
    (r * v / (a * z)) ^ 2 - θ ^ 2 =
      θ ^ 2 * (c - a) / (a * z ^ 2) := by sorry







end D1Bound5
end
