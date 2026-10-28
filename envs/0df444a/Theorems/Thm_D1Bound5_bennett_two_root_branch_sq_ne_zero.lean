-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_root_branch_sq_ne_zero
-- name    : D1Bound5.bennett_two_root_branch_sq_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:55.298502+00:00
-- url     : https://prove2.me/theorems/fafbeea9-2e2c-49b8-82b6-6e3b5bdae4e1
-- title:
--   Bennett two root branch sq ne zero
-- statement:
--   The principal branch used by the two-anchor approximation has the required square and is nonzero throughout the actual size range.
-- source:
--   D1Bound5/BennettRootBranch.lean, lines 5-25, SHA-256 a0ee90a754235b40717fef7f93fd2f0bd9c46c41e8fba43c2c193bb31c76b5b1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
namespace D1Bound5


theorem _root_.D1Bound5.bennett_two_root_branch_sq_ne_zero
    (a c : ℂ) (hsize : 1 < ‖a‖*‖c‖) :
    ((1+1/(a*c))^(1/2 : ℂ))^(2 : ℕ) = 1+1/(a*c) ∧
      (1+1/(a*c))^(1/2 : ℂ) ≠ 0 := by sorry



end D1Bound5
end
