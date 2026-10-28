-- Prove2me | Theorems.Thm_D1Bound5_bennettLocalResidue_sum_eq_remainder_coeff
-- name    : D1Bound5.bennettLocalResidue_sum_eq_remainder_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:04.871346+00:00
-- url     : https://prove2.me/theorems/5e9057e2-7f75-4912-8766-8f2567fe3188
-- title:
--   Bennett Local Residue sum eq remainder coeff
-- statement:
--   For an arbitrary numerator, the sum of the actual local residues is the coefficient one below the denominator degree in its polynomial remainder. The required proper partial fractions are constructed, not assumed.
-- source:
--   D1Bound5/BennettResiduesAtInfinity.lean, lines 122-151, SHA-256 58386256effb45be605c396f13b3729aec81aaca34f62f0de6ccd21675f2e5ad. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.bennettLocalResidue_sum_eq_remainder_coeff
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ) (f : F[X]) :
    ∑ i, bennettLocalResidue a e f i =
      (f %ₘ bennettPoleDenominator a e).coeff ((∑ i, (e i + 1)) - 1) := by sorry











end Residues

end D1Bound5
end
