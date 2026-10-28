-- Prove2me | Theorems.Thm_D1Bound5_finitePTail_adaptive_norm_le
-- name    : D1Bound5.finitePTail_adaptive_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:15.092506+00:00
-- url     : https://prove2.me/theorems/e3843405-4f87-47bf-9c95-0a02e15dffe8
-- title:
--   Finite PTail adaptive norm le
-- statement:
--   Actual adaptive tail estimate. Its coefficient is the positive polynomial obtained from the already-combined integer root columns.
-- source:
--   D1Bound5/FinitePAdaptiveTailBound.lean, lines 100-175, SHA-256 e82a8b4b2fb104b1a8e9ee85e59a9053010935a948dafdd2ad97b98bd358afae. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions

section
namespace D1Bound5








theorem _root_.D1Bound5.finitePTail_adaptive_norm_le (a b s c : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (i : Fin 4) :
    ‖finitePTail a b s c i‖ ≤
      (21/(1024*999) : ℝ)*finitePAdaptiveTailWeight i (‖a‖/‖b‖)*
        ‖s‖^2/(‖a‖^3*‖c‖^5) := by sorry

end D1Bound5
end
