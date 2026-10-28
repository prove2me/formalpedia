-- Prove2me | Theorems.Thm_D1Bound5_bennett_inverse_reverse_coeff
-- name    : D1Bound5.bennett_inverse_reverse_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:45:48.563999+00:00
-- url     : https://prove2.me/theorems/d3a78e74-a43d-45bd-861f-3a276cb6cdef
-- title:
--   Bennett inverse reverse coeff
-- statement:
--   For a monic polynomial of positive degree, coefficients of its reciprocal at infinity are the top coefficients of monomial remainders. The proof uses polynomial reflection, so it introduces no analytic convergence assumption.
-- source:
--   D1Bound5/BennettResiduesAtInfinity.lean, lines 12-89, SHA-256 58386256effb45be605c396f13b3729aec81aaca34f62f0de6ccd21675f2e5ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]


theorem _root_.D1Bound5.bennett_inverse_reverse_coeff
    (D : F[X]) (hD : D.Monic) (hd : 0 < D.natDegree)
    (H : PowerSeries F) (hH : (D.reverse : PowerSeries F) * H = 1) (t : ℕ) :
    PowerSeries.coeff t H =
      ((X ^ (D.natDegree - 1 + t)) %ₘ D).coeff (D.natDegree - 1) := by sorry

end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]

















end Residues

end D1Bound5
end
