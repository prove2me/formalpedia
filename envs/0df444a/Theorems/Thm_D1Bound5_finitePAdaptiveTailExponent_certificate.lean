-- Prove2me | Theorems.Thm_D1Bound5_finitePAdaptiveTailExponent_certificate
-- name    : D1Bound5.finitePAdaptiveTailExponent_certificate
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:05.489063+00:00
-- url     : https://prove2.me/theorems/68ce4650-0ae4-4bb2-8978-8529db054191
-- title:
--   Finite PAdaptive Tail Exponent certificate
-- statement:
--   Every concrete term meets the exponent inequalities used by the adaptive scalar estimate. Zero padding also satisfies these inequalities.
-- source:
--   D1Bound5/FinitePAdaptiveTailData.lean, lines 28-38, SHA-256 7413f6f034f62f29a71bf7601fa054eb71ec31e2a6c85f06e6f3607c6aab796c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePHeight_Definitions

section
namespace D1Bound5








theorem _root_.D1Bound5.finitePAdaptiveTailExponent_certificate (i : Fin 4) (l j t : Fin 3) :
    let u := finitePRootTerms i l j t
    u.2.1+u.2.2.1+u.2.2.2+3 ≤ (4+(l : ℕ))+2 ∧
    (j=0 → finitePAdaptiveTailExponent i l j t+u.2.2.1+u.2.2.2=2) ∧
    (j=1 → finitePAdaptiveTailExponent i l j t+u.2.2.1+u.2.2.2=(4+(l : ℕ))+2 ∧
      u.2.2.2 ≤ 2) ∧
    (j=2 → finitePAdaptiveTailExponent i l j t+u.2.2.1+u.2.2.2=(4+(l : ℕ))+2) := by sorry



end D1Bound5
end
