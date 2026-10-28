-- Prove2me | Theorems.Thm_D1Bound5_finitePAdaptiveTailWeight_eq
-- name    : D1Bound5.finitePAdaptiveTailWeight_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:19.246896+00:00
-- url     : https://prove2.me/theorems/b3937b57-6ac5-4fa6-9a69-98efbbe499cb
-- title:
--   Finite PAdaptive Tail Weight eq
-- statement:
--   The four positive polynomials are computed from the actual integer coefficient lists after the H and V cancellations.
-- source:
--   D1Bound5/FinitePAdaptiveTailData.lean, lines 16-26, SHA-256 7413f6f034f62f29a71bf7601fa054eb71ec31e2a6c85f06e6f3607c6aab796c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.finitePAdaptiveTailWeight_eq (i : Fin 4) (x : ℝ) :
    finitePAdaptiveTailWeight i x =
      ![295*x+143*x^2+143*x^4+295*x^5,
        590*(x+x^4+x^5),
        885+1144*x+435*x^2+42*x^3+170*x^4,
        885+1144*x+435*x^2+2634*x^3+170*x^4] i := by sorry





end D1Bound5
end
