-- Prove2me | Theorems.Thm_D1Bound5_bennettReciprocalInfinity_mul
-- name    : D1Bound5.bennettReciprocalInfinity_mul
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:35:51.957342+00:00
-- url     : https://prove2.me/theorems/68722982-790f-4712-aa56-a625b335a6fe
-- title:
--   Bennett Reciprocal Infinity mul
-- statement:
--   The explicit product at infinity really inverts the reversed denominator.
-- source:
--   D1Bound5/BennettResiduesAtInfinity.lean, lines 172-198, SHA-256 58386256effb45be605c396f13b3729aec81aaca34f62f0de6ccd21675f2e5ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
import Definitions.Def_D1Bound5_BennettResiduesAtInfinity_Definitions

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]



end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]














theorem _root_.D1Bound5.bennettReciprocalInfinity_mul
    (a : ι → F) (e : ι → ℕ) :
    ((bennettPoleDenominator a e).reverse : PowerSeries F) *
      bennettReciprocalInfinity a e = 1 := by sorry



end Residues

end D1Bound5
end
