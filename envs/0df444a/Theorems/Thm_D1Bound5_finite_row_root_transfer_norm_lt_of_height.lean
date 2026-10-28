-- Prove2me | Theorems.Thm_D1Bound5_finite_row_root_transfer_norm_lt_of_height
-- name    : D1Bound5.finite_row_root_transfer_norm_lt_of_height
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:13.765654+00:00
-- url     : https://prove2.me/theorems/31584477-4bac-41c4-8ebb-9686ed22deee
-- title:
--   Finite row root transfer norm lt of height
-- statement:
--   An intermediate analytic transfer for finite integral rows. It states only the triangle-inequality step with strict height: each application must provide its actual coefficients, residual estimate, and signed root errors.
-- source:
--   D1Bound5/FiniteRowRootTransferHeight.lean, lines 7-62, SHA-256 ea43ae94c1dccd32600b727f02668476246e694d42d50b3a88de517a4354c98e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.finite_row_root_transfer_norm_lt_of_height
    {I : Type*} [Fintype I] (q0 z : ℂ) (a p theta s : I → ℂ)
    (ha : ∀ j, a j ≠ 0) (hz : z ≠ 0) (E H R : ℝ) (hE : 0 < E)
    (herr : ∀ j, ‖theta j-s j/(a j*z)‖ ≤ E/(‖a j‖*‖z‖^2))
    (hheight : (∑ j, ‖p j‖) < H)
    (hres : ‖q0+∑ j, a j*p j*theta j‖ ≤ R) :
    ‖q0*z+∑ j, p j*s j‖ < R*‖z‖+E*H/‖z‖ := by sorry

end D1Bound5
end
