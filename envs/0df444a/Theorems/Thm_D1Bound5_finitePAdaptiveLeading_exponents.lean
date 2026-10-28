-- Prove2me | Theorems.Thm_D1Bound5_finitePAdaptiveLeading_exponents
-- name    : D1Bound5.finitePAdaptiveLeading_exponents
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:32.892897+00:00
-- url     : https://prove2.me/theorems/c1d2c821-bd20-49aa-96e7-fc1450777fac
-- title:
--   Finite PAdaptive Leading exponents
-- statement:
--   Auxiliary result `finitePAdaptiveLeading_exponents` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePAdaptiveLeading.lean, lines 43-52, SHA-256 eb474c59b02738fa364b083f7c3f854ab6e1f57dae76acf74969fb1b0dcbbac0. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePAdaptiveLeading_Definitions
import Definitions.Def_D1Bound5_FinitePLeadingBound_Definitions

section
namespace D1Bound5













theorem _root_.D1Bound5.finitePAdaptiveLeading_exponents (i : Fin 4) (t : Fin 12) :
    let u := finitePAdaptiveLeadingTerms i t
    let p := finitePLeadingNumeratorExponent u
    p 0+p 1+p 2+3 ≤ u.2.2.2.2+2 ∧
      finitePLeadingRatioExponent u+p 1+p 2 = (if u.2.1=0 then 2 else u.2.2.2.2+2) ∧
      (u.2.1 ≠ 2 → p 2 ≤ 2) := by sorry





end D1Bound5
end
