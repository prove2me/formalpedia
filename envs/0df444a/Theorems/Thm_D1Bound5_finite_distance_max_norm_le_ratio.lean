-- Prove2me | Theorems.Thm_D1Bound5_finite_distance_max_norm_le_ratio
-- name    : D1Bound5.finite_distance_max_norm_le_ratio
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:47.647667+00:00
-- url     : https://prove2.me/theorems/6469a774-fe23-4acb-954d-01f04c58869c
-- title:
--   Finite distance max norm le ratio
-- statement:
--   Exact distance envelope valid even when the two anchors are close. The second maximum term handles the row whose cleared divisor is the anchor rather than the anchor difference.
-- source:
--   D1Bound5/FiveRegionResidualRates.lean, lines 5-22, SHA-256 01fe8d49e37f2988c9a084ee7c0a592dd520f83f3552000c7c542c8985d8dfb4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.finite_distance_max_norm_le_ratio (x y : ℂ) (r : ℝ) (n : ℕ)
    (hr : 0 ≤ r) (hn : 1 ≤ n) (hxy : ‖x‖ ≤ r*‖y‖) :
    max (‖x-y‖^n) (‖x‖*‖x-y‖^(n-1)) ≤ (1+r)^n*‖y‖^n := by sorry



end D1Bound5
end
