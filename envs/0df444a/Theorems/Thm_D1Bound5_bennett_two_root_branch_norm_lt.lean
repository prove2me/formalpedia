-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_root_branch_norm_lt
-- name    : D1Bound5.bennett_two_root_branch_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:23:26.942408+00:00
-- url     : https://prove2.me/theorems/d31dbc19-da4f-41cd-b706-9f32938b8b1b
-- title:
--   Bennett two root branch norm lt
-- statement:
--   A uniform bound on the same actual branch. The weak rational constant is chosen to leave room in the later signed-root approximation.
-- source:
--   D1Bound5/BennettRootBranch.lean, lines 27-42, SHA-256 a0ee90a754235b40717fef7f93fd2f0bd9c46c41e8fba43c2c193bb31c76b5b1. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.bennett_two_root_branch_norm_lt
    (a c : ℂ) (hsize : 1000 ≤ ‖a‖*‖c‖) :
    ‖(1+1/(a*c))^(1/2 : ℂ)‖ < (6/5 : ℝ) := by sorry

end D1Bound5
end
