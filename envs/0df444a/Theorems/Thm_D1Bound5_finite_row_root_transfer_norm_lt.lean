-- Prove2me | Theorems.Thm_D1Bound5_finite_row_root_transfer_norm_lt
-- name    : D1Bound5.finite_row_root_transfer_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:54.033073+00:00
-- url     : https://prove2.me/theorems/686ad586-bffd-4796-828c-f1ce8cd1df50
-- title:
--   Finite row root transfer norm lt
-- statement:
--   An intermediate analytic transfer for finite integral rows. It states only the triangle-inequality step: each application must provide its actual coefficients, residual estimate, and signed root errors.
-- source:
--   D1Bound5/FiniteRowRootTransfer.lean, lines 7-61, SHA-256 4495cbe4dcaa55c3acb6a9939094800f79ebe9bac6aca2a6a2211f0d73fd1306. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.finite_row_root_transfer_norm_lt
    {I : Type*} [Fintype I] (q0 z : ℂ) (a p theta s : I → ℂ)
    (ha : ∀ j, a j ≠ 0) (hz : z ≠ 0) (E H R : ℝ) (hE : 0 ≤ E)
    (herr : ∀ j, ‖theta j-s j/(a j*z)‖ ≤ E/(‖a j‖*‖z‖^2))
    (hheight : (∑ j, ‖p j‖) ≤ H)
    (hres : ‖q0+∑ j, a j*p j*theta j‖ < R) :
    ‖q0*z+∑ j, p j*s j‖ < R*‖z‖+E*H/‖z‖ := by sorry

end D1Bound5
end
