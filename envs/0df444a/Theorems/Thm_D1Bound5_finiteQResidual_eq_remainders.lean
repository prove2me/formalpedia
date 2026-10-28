-- Prove2me | Theorems.Thm_D1Bound5_finiteQResidual_eq_remainders
-- name    : D1Bound5.finiteQResidual_eq_remainders
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:13.392232+00:00
-- url     : https://prove2.me/theorems/71889ad1-9378-4e3e-a780-02b2dabe7117
-- title:
--   Finite QResidual eq remainders
-- statement:
--   Every nonnegative power and each inverse power through c^-3 cancels. The remaining four terms are genuine analytic remainders, not an assumed formal residual estimate.
-- source:
--   D1Bound5/FiniteQResidualIdentity.lean, lines 80-97, SHA-256 74ab040376af9b42e7ee62656f2fd8f3a92a0111248e8b31465d43a74a137c58. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions

section
open Finset

namespace D1Bound5









set_option maxHeartbeats 800000 in

theorem _root_.D1Bound5.finiteQResidual_eq_remainders
    (u v c : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0) :
    finiteQResidual u v c =
      u*(u^2-5*u*v)*finiteQHalfRemainder 4 (1/(u*c)) +
      u*(4*u^3-8*u^2*v)*c*finiteQHalfRemainder 5 (1/(u*c)) +
      v*(5*u*v-v^2)*finiteQHalfRemainder 4 (1/(v*c)) +
      v*(8*u*v^2-4*v^3)*c*finiteQHalfRemainder 5 (1/(v*c)) := by sorry

end D1Bound5
end
