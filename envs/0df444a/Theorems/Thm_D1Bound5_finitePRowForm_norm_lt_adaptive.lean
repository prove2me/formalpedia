-- Prove2me | Theorems.Thm_D1Bound5_finitePRowForm_norm_lt_adaptive
-- name    : D1Bound5.finitePRowForm_norm_lt_adaptive
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:26:18.334844+00:00
-- url     : https://prove2.me/theorems/b3f1709f-663d-47ac-bf87-e27efc846806
-- title:
--   Finite PRow Form norm lt adaptive
-- statement:
--   Auxiliary result `finitePRowForm_norm_lt_adaptive` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePAdaptiveRowBound.lean, lines 9-36, SHA-256 9454ef9c7b4fbe3699f269f0a5d444a111bff66cf8dea64ecb619af96e38a881. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FinitePIntegralRows_Definitions

section
namespace D1Bound5

theorem _root_.D1Bound5.finitePRowForm_norm_lt_adaptive (a b s c z rA rB rS : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hz : z ≠ 0)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hC : 200 ≤ ‖c‖) (hAC : 1000 ≤ ‖a‖*‖c‖)
    (q : ℝ) (hq : 1 ≤ q) (hqab : q*‖a‖ ≤ ‖b‖)
    (herr : ∀ j : Fin 3,
      ‖(1+1/(![a,b,s] j*c))^(1/2 : ℂ)-![rA,rB,rS] j/(![a,b,s] j*z)‖ ≤
        (101/100 : ℝ)*‖c‖/(‖![a,b,s] j‖*‖z‖^2)) (i : Fin 4) :
    ‖finitePRowForm a b s c z rA rB rS i‖ <
      2400*max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*‖c‖^3/‖z‖+
        finitePAdaptiveRate (1/q)*‖s‖^2*‖z‖/(‖a‖^3*‖c‖^5) := by sorry

end D1Bound5
end
