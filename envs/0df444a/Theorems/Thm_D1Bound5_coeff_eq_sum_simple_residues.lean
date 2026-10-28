-- Prove2me | Theorems.Thm_D1Bound5_coeff_eq_sum_simple_residues
-- name    : D1Bound5.coeff_eq_sum_simple_residues
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:41.437745+00:00
-- url     : https://prove2.me/theorems/8a264138-52e5-4c3a-829a-e373c8544f04
-- title:
--   Coeff eq sum simple residues
-- statement:
--   The coefficient one below the denominator degree is the sum of the simple-pole coefficients in an exact cleared partial-fraction identity. The identity itself is an explicit hypothesis, not inferred from notation.
-- source:
--   D1Bound5/BennettResidueCoefficient.lean, lines 73-87, SHA-256 8c207032d119b0629e3cee3a36cfe0f7dd94d73784c8b28b8cba78efa262f829. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.coeff_eq_sum_simple_residues (a : ι → R) (e : ι → ℕ)
    (c : (i : ι) → Fin (e i + 1) → R) (f : R[X])
    (hdecomp : f = ∑ i, ∑ j : Fin (e i + 1),
      C (c i j) * clearedPoleNumerator a e i j) :
    f.coeff ((∑ l, (e l + 1)) - 1) = ∑ i, c i (Fin.last (e i)) := by sorry



end CommRing

end D1Bound5
end
