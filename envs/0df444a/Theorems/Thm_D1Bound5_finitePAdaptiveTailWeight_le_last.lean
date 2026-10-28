-- Prove2me | Theorems.Thm_D1Bound5_finitePAdaptiveTailWeight_le_last
-- name    : D1Bound5.finitePAdaptiveTailWeight_le_last
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:18.944088+00:00
-- url     : https://prove2.me/theorems/6b356786-0534-4e26-ab3e-66479ebf34b8
-- title:
--   Finite PAdaptive Tail Weight le last
-- statement:
--   Auxiliary result `finitePAdaptiveTailWeight_le_last` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePAdaptiveResidual.lean, lines 19-29, SHA-256 25fa69daa14e28209c09660c5858b952ff9e39422be6b297ad69d024782cb11b. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5





theorem _root_.D1Bound5.finitePAdaptiveTailWeight_le_last (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (i : Fin 4) : finitePAdaptiveTailWeight i x ≤ finitePAdaptiveTailWeight 3 x := by sorry









end D1Bound5
end
