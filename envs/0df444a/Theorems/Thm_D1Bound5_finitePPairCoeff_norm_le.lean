-- Prove2me | Theorems.Thm_D1Bound5_finitePPairCoeff_norm_le
-- name    : D1Bound5.finitePPairCoeff_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:58.689362+00:00
-- url     : https://prove2.me/theorems/26ba0bbb-d945-425b-aafa-9372349e3a23
-- title:
--   Finite PPair Coeff norm le
-- statement:
--   Coefficient-height control with the exact reciprocal-anchor power needed by its Taylor remainder, proved term by term from integer data.
-- source:
--   D1Bound5/FinitePTailCoefficients.lean, lines 47-86, SHA-256 48599cb8aa9aff9768b21efa168c2d0d2e6b70cc69039e6172943d1904229fb4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePTailCoefficients_Definitions

section
namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three












theorem _root_.D1Bound5.finitePPairCoeff_norm_le (u v : ℂ) (A S : ℝ)
    (hA1 : 1 ≤ A) (hAu : A ≤ ‖u‖) (hAv : A ≤ ‖v‖)
    (huS : ‖u‖ ≤ S) (hvS : ‖v‖ ≤ S)
    (kind side : Fin 2) (l : Fin 3) :
    ‖finitePPairCoeff u v kind side l‖ ≤
      (finitePTailCoeffWeight kind side l : ℝ)*(S^2/A^4)*
        ‖![u,v] side‖^(5+(l : ℕ)) := by sorry

end D1Bound5
end
