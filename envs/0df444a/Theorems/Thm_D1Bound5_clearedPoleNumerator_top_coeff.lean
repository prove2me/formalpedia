-- Prove2me | Theorems.Thm_D1Bound5_clearedPoleNumerator_top_coeff
-- name    : D1Bound5.clearedPoleNumerator_top_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:47.898208+00:00
-- url     : https://prove2.me/theorems/8c2de7bd-994c-4a4f-9efd-4513f2a0b9b1
-- title:
--   Cleared Pole Numerator top coeff
-- statement:
--   At degree one below the denominator degree, only the cleared simple pole has a nonzero coefficient. This calculation does not require distinct nodes.
-- source:
--   D1Bound5/BennettResidueCoefficient.lean, lines 46-71, SHA-256 8c207032d119b0629e3cee3a36cfe0f7dd94d73784c8b28b8cba78efa262f829. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions

section
open Finset Polynomial

namespace D1Bound5

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]








theorem _root_.D1Bound5.clearedPoleNumerator_top_coeff (a : ι → R) (e : ι → ℕ)
    (i : ι) (j : Fin (e i + 1)) :
    (clearedPoleNumerator a e i j).coeff ((∑ l, (e l + 1)) - 1) =
      if j = Fin.last (e i) then 1 else 0 := by sorry





end CommRing

end D1Bound5
end
