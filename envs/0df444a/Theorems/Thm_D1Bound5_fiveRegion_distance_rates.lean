-- Prove2me | Theorems.Thm_D1Bound5_fiveRegion_distance_rates
-- name    : D1Bound5.fiveRegion_distance_rates
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:18:28.367519+00:00
-- url     : https://prove2.me/theorems/02abc16b-7a3f-4030-b24d-1934a328e74b
-- title:
--   Five Region distance rates
-- statement:
--   All five finite residual rates are derived from actual anchor moduli, with no lower bound on their separation.
-- source:
--   D1Bound5/FiveRegionResidualRates.lean, lines 24-45, SHA-256 01fe8d49e37f2988c9a084ee7c0a592dd520f83f3552000c7c542c8985d8dfb4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.fiveRegion_distance_rates (region : Fin 5) (x y : ℂ)
    (hxy : ‖x‖ ≤ fiveRegionAnchorRatio region*‖y‖) :
    (101/2560 : ℝ)*max (‖x-y‖^4) (‖x‖*‖x-y‖^3) ≤ fiveRegionN2Residual region*‖y‖^4 ∧
    (3535/409600 : ℝ)*max (‖x-y‖^6) (‖x‖*‖x-y‖^5) ≤ fiveRegionN3Residual region*‖y‖^6 ∧
    (707/40960 : ℝ)*max (‖x-y‖^6) (‖x‖*‖x-y‖^5) ≤ fiveRegionA3Residual region*‖y‖^6 ∧
    (6363/409600 : ℝ)*max (‖x-y‖^8) (‖x‖*‖x-y‖^7) ≤ fiveRegionA4Residual region*‖y‖^8 ∧
    (9999/2621440 : ℝ)*max (‖x-y‖^10) (‖x‖*‖x-y‖^9) ≤ fiveRegionA5Residual region*‖y‖^10 := by sorry

end D1Bound5
end
