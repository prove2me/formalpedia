-- Prove2me | Theorems.Thm_D1Bound5_bennettLocalResidue_eq_decomposition_coeff
-- name    : D1Bound5.bennettLocalResidue_eq_decomposition_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:20.95999+00:00
-- url     : https://prove2.me/theorems/0c237867-9e85-4135-a450-b7e514cd09c2
-- title:
--   Bennett Local Residue eq decomposition coeff
-- statement:
--   The concrete local series coefficient equals the simple-pole coefficient in any exact cleared decomposition.
-- source:
--   D1Bound5/BennettLocalResidues.lean, lines 92-121, SHA-256 69884bc84f14bf065cb46a21f71bb9f253dca11c8d085058e033df4ac0004d31. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]




















theorem _root_.D1Bound5.bennettLocalResidue_eq_decomposition_coeff
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ)
    (c : (l : ι) → Fin (e l + 1) → F) (f : Polynomial F)
    (hc : f = ∑ l, ∑ j : Fin (e l + 1),
      Polynomial.C (c l j) * clearedPoleNumerator a e l j) (i : ι) :
    bennettLocalResidue a e f i = c i (Fin.last (e i)) := by sorry



end Field

end D1Bound5
end
