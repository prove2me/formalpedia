-- Prove2me | Theorems.Thm_D1Bound5_bennettLocalReciprocal_mul
-- name    : D1Bound5.bennettLocalReciprocal_mul
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:26.384991+00:00
-- url     : https://prove2.me/theorems/38330df7-1ae1-4c8a-ba29-11674af9ea48
-- title:
--   Bennett Local Reciprocal mul
-- statement:
--   Auxiliary result `bennettLocalReciprocal_mul` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/BennettLocalResidues.lean, lines 42-52, SHA-256 69884bc84f14bf065cb46a21f71bb9f253dca11c8d085058e033df4ac0004d31. Project: https://github.com/tomislav-math/d1-bound5-lean

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











theorem _root_.D1Bound5.bennettLocalReciprocal_mul (a : ι → F) (ha : Function.Injective a)
    (e : ι → ℕ) (i : ι) :
    (∏ l ∈ (Finset.univ : Finset ι).erase i,
      (PowerSeries.C (a i - a l) + PowerSeries.X) ^ (e l + 1)) *
        bennettLocalReciprocal a e i = 1 := by sorry











end Field

end D1Bound5
end
