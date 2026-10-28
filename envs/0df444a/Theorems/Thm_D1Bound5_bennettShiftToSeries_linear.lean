-- Prove2me | Theorems.Thm_D1Bound5_bennettShiftToSeries_linear
-- name    : D1Bound5.bennettShiftToSeries_linear
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:38.945917+00:00
-- url     : https://prove2.me/theorems/5cff10ae-8640-45b2-b65b-e6a55b3e69e2
-- title:
--   Bennett Shift To Series linear
-- statement:
--   Auxiliary result `bennettShiftToSeries_linear` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/BennettLocalResidues.lean, lines 21-27, SHA-256 69884bc84f14bf065cb46a21f71bb9f253dca11c8d085058e033df4ac0004d31. Project: https://github.com/tomislav-math/d1-bound5-lean

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





@[simp] theorem _root_.D1Bound5.bennettShiftToSeries_linear (b c : F) :
    bennettShiftToSeries b (Polynomial.X - Polynomial.C c) =
      PowerSeries.C (b - c) + PowerSeries.X := by sorry

















end Field

end D1Bound5
end
