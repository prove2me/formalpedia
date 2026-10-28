-- Prove2me | Theorems.Thm_D1Bound5_bennettLocalResidue_sum_X_pow_eq_infinity_coeff
-- name    : D1Bound5.bennettLocalResidue_sum_X_pow_eq_infinity_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:36.048594+00:00
-- url     : https://prove2.me/theorems/a1d35115-17ea-4ed4-9209-e51ed052a689
-- title:
--   Bennett Local Residue sum X pow eq infinity coeff
-- statement:
--   Exact all-orders residue identity above the cancellation threshold. The low-degree zero-residue theorem and this formula together determine every coefficient of the actual Bennett row residual.
-- source:
--   D1Bound5/BennettResiduesAtInfinity.lean, lines 200-213, SHA-256 58386256effb45be605c396f13b3729aec81aaca34f62f0de6ccd21675f2e5ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
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
















theorem _root_.D1Bound5.bennettLocalResidue_sum_X_pow_eq_infinity_coeff
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ)
    (hd : 0 < ∑ i, (e i + 1)) (t : ℕ) :
    ∑ i, bennettLocalResidue a e (X ^ ((∑ l, (e l + 1)) - 1 + t)) i =
      PowerSeries.coeff t (bennettReciprocalInfinity a e) := by sorry

end Residues

end D1Bound5
end
