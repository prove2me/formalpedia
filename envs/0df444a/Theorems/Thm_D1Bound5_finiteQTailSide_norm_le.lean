-- Prove2me | Theorems.Thm_D1Bound5_finiteQTailSide_norm_le
-- name    : D1Bound5.finiteQTailSide_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:53.028745+00:00
-- url     : https://prove2.me/theorems/316852e0-50e6-4f86-b530-e6d3cebbe4ed
-- title:
--   Finite QTail Side norm le
-- statement:
--   Each of the two anchor sides is bounded using its actual fourth- and fifth-order Taylor tails. Cancellation of the anchor and c powers leaves exactly the monomials1/U and V/U².
-- source:
--   D1Bound5/FiniteQResidualBound.lean, lines 19-94, SHA-256 a3e6f379d6e8b22749f6d6447d2c163488ae6d9c3b3948f32b3749f0bb7a7bac. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQResidualBound_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.finiteQTailSide_norm_le
    (u v c : ℂ) (A T : ℝ) (hA : 0 < A)
    (hAu : A ≤ ‖u‖) (huT : ‖u‖ ≤ T) (hvT : ‖v‖ ≤ T)
    (hAC : 1000 ≤ A*‖c‖) :
    ‖finiteQTailSide u v c‖ ≤ (625/888 : ℝ)*T/(A^2*‖c‖^4) := by sorry



end D1Bound5
end
