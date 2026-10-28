-- Prove2me | Theorems.Thm_D1Bound5_finiteP_residual_norm_le_adaptive
-- name    : D1Bound5.finiteP_residual_norm_le_adaptive
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:15.200452+00:00
-- url     : https://prove2.me/theorems/43958176-bccd-4837-9288-0fffb6fa562f
-- title:
--   Finite P residual norm le adaptive
-- statement:
--   Exact adaptive bound on the actual principal-root residual.
-- source:
--   D1Bound5/FinitePAdaptiveResidual.lean, lines 46-84, SHA-256 25fa69daa14e28209c09660c5858b952ff9e39422be6b297ad69d024782cb11b. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions

section
namespace D1Bound5














theorem _root_.D1Bound5.finiteP_residual_norm_le_adaptive (a b s c : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (q : ℝ) (hq : 1 ≤ q) (hqab : q*‖a‖ ≤ ‖b‖)
    (i : Fin 4) :
    ‖finitePResidual a b s c i‖ ≤
      finitePAdaptiveRate (1/q)*‖s‖^2/(‖a‖^3*‖c‖^5) := by sorry

end D1Bound5
end
