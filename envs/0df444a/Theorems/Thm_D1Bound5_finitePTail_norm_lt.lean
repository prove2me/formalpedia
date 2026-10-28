-- Prove2me | Theorems.Thm_D1Bound5_finitePTail_norm_lt
-- name    : D1Bound5.finitePTail_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:47:42.537683+00:00
-- url     : https://prove2.me/theorems/74731bfa-b207-4270-a5bc-58f2b7a203d9
-- title:
--   Finite PTail norm lt
-- statement:
--   Every actual P-row tail is strictly below one eighth of the common residual scale. No coefficient or analytic bound is assumed in the statement.
-- source:
--   D1Bound5/FinitePTailBound.lean, lines 80-132, SHA-256 ab0bc04a98f79bcb424f4bb78f9ebf8d6779a1a1bf51c7bd6e2f84df375808ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.finitePTail_norm_lt (a b s c : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (i : Fin 4) :
    ‖finitePTail a b s c i‖ < (1/8 : ℝ)*‖s‖^2/(‖a‖^3*‖c‖^5) := by sorry

end D1Bound5
end
