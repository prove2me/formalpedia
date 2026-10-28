-- Prove2me | Theorems.Thm_D1Bound5_finitePHalfRemainder_norm_le
-- name    : D1Bound5.finitePHalfRemainder_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:41:47.347421+00:00
-- url     : https://prove2.me/theorems/b5ec522d-0dd8-4b77-8de0-e928c9288f76
-- title:
--   Finite PHalf Remainder norm le
-- statement:
--   Degree-six tail estimate for the actual principal half power.
-- source:
--   D1Bound5/FinitePResidualIdentity.lean, lines 29-62, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three




theorem _root_.D1Bound5.finitePHalfRemainder_norm_le (n : ℕ) (z : ℂ)
    (hn : 6 ≤ n) (hz : ‖z‖ < 1) :
    ‖finiteQHalfRemainder n z‖ ≤ (21/1024 : ℝ)*‖z‖^n/(1-‖z‖) := by sorry































end D1Bound5
end
