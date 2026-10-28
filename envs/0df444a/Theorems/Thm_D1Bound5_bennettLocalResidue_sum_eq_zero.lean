-- Prove2me | Theorems.Thm_D1Bound5_bennettLocalResidue_sum_eq_zero
-- name    : D1Bound5.bennettLocalResidue_sum_eq_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:14.05386+00:00
-- url     : https://prove2.me/theorems/89db08f6-8367-45bb-9cf7-38315cacf7ff
-- title:
--   Bennett Local Residue sum eq zero
-- statement:
--   The sum of the explicitly defined local residues vanishes whenever the numerator has degree at least two below the full denominator degree. No decomposition or cancellation identity is assumed.
-- source:
--   D1Bound5/BennettLocalResidues.lean, lines 123-137, SHA-256 69884bc84f14bf065cb46a21f71bb9f253dca11c8d085058e033df4ac0004d31. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]






















theorem _root_.D1Bound5.bennettLocalResidue_sum_eq_zero (a : ι → F) (ha : Function.Injective a)
    (e : ι → ℕ) (f : Polynomial F)
    (hdeg : f.degree < ((∑ l, (e l + 1)) - 1 : ℕ)) :
    ∑ i, bennettLocalResidue a e f i = 0 := by sorry

end Field

end D1Bound5
end
