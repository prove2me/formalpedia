-- Prove2me | Theorems.Thm_D1Bound5_finiteP_residual_norm_lt
-- name    : D1Bound5.finiteP_residual_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:08.655706+00:00
-- url     : https://prove2.me/theorems/03d44ae6-a352-4785-8e62-f3c990af92c7
-- title:
--   Finite P residual norm lt
-- statement:
--   The actual four-row P residual has the uniform manuscript constant3. The proof uses finite Taylor cancellation and a convergent geometric tail.
-- source:
--   D1Bound5/FinitePResidualBound.lean, lines 6-38, SHA-256 2e26188590dc39db7d145b2ac9f811d16c48660fef1b96912b408e4144f795e6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.finiteP_residual_norm_lt (a b s c : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (i : Fin 4) :
    ‖finitePResidual a b s c i‖ < 3*‖s‖^2/(‖a‖^3*‖c‖^5) := by sorry

end D1Bound5
end
