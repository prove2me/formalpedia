-- Prove2me | Theorems.Thm_D1Bound5_bennettLocalResidue_eq_zero_of_denominator_dvd
-- name    : D1Bound5.bennettLocalResidue_eq_zero_of_denominator_dvd
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:43.349996+00:00
-- url     : https://prove2.me/theorems/c21a7bd2-c5e4-4f51-906c-97bd1b39b8ea
-- title:
--   Bennett Local Residue eq zero of denominator dvd
-- statement:
--   A numerator divisible by the full denominator has zero local residue. This includes the polynomial part of an improper partial fraction.
-- source:
--   D1Bound5/BennettResiduesAtInfinity.lean, lines 98-114, SHA-256 58386256effb45be605c396f13b3729aec81aaca34f62f0de6ccd21675f2e5ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions

section
open Finset Polynomial

namespace D1Bound5

section Reverse

variable {F : Type*} [Field F]



end Reverse

section Residues

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]


theorem _root_.D1Bound5.bennettLocalResidue_eq_zero_of_denominator_dvd
    (a : ι → F) (e : ι → ℕ) (f : F[X])
    (hf : bennettPoleDenominator a e ∣ f) (i : ι) :
    bennettLocalResidue a e f i = 0 := by sorry















end Residues

end D1Bound5
end
