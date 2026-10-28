-- Prove2me | Theorems.Thm_D1Bound5_finiteQHalfRemainder_norm_le
-- name    : D1Bound5.finiteQHalfRemainder_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:44.586752+00:00
-- url     : https://prove2.me/theorems/347a3f92-2ff7-4903-9c7e-ee17c9ccf563
-- title:
--   Finite QHalf Remainder norm le
-- statement:
--   A convergent geometric envelope for the actual half-power remainder, valid from degree four onward with the sharp coefficient5/128.
-- source:
--   D1Bound5/FiniteQResidualIdentity.lean, lines 34-71, SHA-256 74ab040376af9b42e7ee62656f2fd8f3a92a0111248e8b31465d43a74a137c58. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.finiteQHalfRemainder_norm_le (n : ℕ) (z : ℂ)
    (hn : 4 ≤ n) (hz : ‖z‖ < 1) :
    ‖finiteQHalfRemainder n z‖ ≤ (5/128 : ℝ)*‖z‖^n/(1-‖z‖) := by sorry





end D1Bound5
end
