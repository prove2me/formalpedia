-- Prove2me | Theorems.Thm_D1Bound5_bennettResidueTaylor_homogenize
-- name    : D1Bound5.bennettResidueTaylor_homogenize
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:04.979175+00:00
-- url     : https://prove2.me/theorems/dc865166-7e2e-4b93-9790-24959fada1f5
-- title:
--   Bennett Residue Taylor homogenize
-- statement:
--   Clearing the common N denominator recovers the polynomial G used in the node-removal determinant induction.
-- source:
--   D1Bound5/BennettResiduePolynomials.lean, lines 57-74, SHA-256 5264fd8f08d4a6fb748bab8f101f05ca183c3e4658b02954972b81e086f0144d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]








theorem _root_.D1Bound5.bennettResidueTaylor_homogenize (k r : ℕ) (hr : r ≤ k)
    (ν a N : F) (B : PowerSeries F) (hN : N ≠ 0) :
    N ^ k * (bennettResidueTaylor k r ν a B).eval N⁻¹ =
      (bennettClearedTaylor k r ν a B).eval N := by sorry

section Nodes

variable {I : Type*} [DecidableEq I]







end Nodes

end D1Bound5
end
