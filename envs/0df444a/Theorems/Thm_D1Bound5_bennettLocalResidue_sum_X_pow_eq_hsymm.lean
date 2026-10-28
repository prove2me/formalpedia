-- Prove2me | Theorems.Thm_D1Bound5_bennettLocalResidue_sum_X_pow_eq_hsymm
-- name    : D1Bound5.bennettLocalResidue_sum_X_pow_eq_hsymm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:12.108989+00:00
-- url     : https://prove2.me/theorems/7f3ac699-6655-4687-87a6-f2920d42c008
-- title:
--   Bennett Local Residue sum X pow eq hsymm
-- statement:
--   The actual high-degree residue sum is a complete homogeneous polynomial on repeated nodes, supplying the exact input to the Bennett tail majorant.
-- source:
--   D1Bound5/BennettRepeatedHsymm.lean, lines 137-147, SHA-256 2c35125785b6ff0c9b69a4236b7a718a4b75a5a68706b7a3ada2c46efaddc905. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions
import Definitions.Def_D1Bound5_BennettRepeatedHsymm_Definitions

section
open Finset

namespace D1Bound5

section Homogeneous

variable {R ι : Type*} [CommRing R] [DecidableEq ι]









end Homogeneous

section Repeated

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]












theorem _root_.D1Bound5.bennettLocalResidue_sum_X_pow_eq_hsymm
    (a : ι → F) (ha : Function.Injective a) (e : ι → ℕ)
    (hd : 0 < ∑ i, (e i + 1)) (t : ℕ) :
    ∑ i, bennettLocalResidue a e
        (Polynomial.X ^ ((∑ l, (e l + 1)) - 1 + t)) i =
      MvPolynomial.aeval (fun i : BennettRepeatedNodes e => a i.1)
        (MvPolynomial.hsymm (BennettRepeatedNodes e) F t) := by sorry

end Repeated

end D1Bound5
end
