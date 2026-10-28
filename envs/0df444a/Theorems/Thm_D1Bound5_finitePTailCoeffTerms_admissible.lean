-- Prove2me | Theorems.Thm_D1Bound5_finitePTailCoeffTerms_admissible
-- name    : D1Bound5.finitePTailCoeffTerms_admissible
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:18.213007+00:00
-- url     : https://prove2.me/theorems/0fe1a190-f9ec-4f1b-81d2-08b457b9a469
-- title:
--   Finite PTail Coeff Terms admissible
-- statement:
--   Auxiliary result `finitePTailCoeffTerms_admissible` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePTailCoefficients.lean, lines 27-31, SHA-256 48599cb8aa9aff9768b21efa168c2d0d2e6b70cc69039e6172943d1904229fb4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePTailCoefficients_Definitions

section
namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three





theorem _root_.D1Bound5.finitePTailCoeffTerms_admissible (kind side : Fin 2) (l t : Fin 3) :
    (finitePTailCoeffTerms kind side l t).2.2 ≤ 2 ∧
      (finitePTailCoeffTerms kind side l t).2.1+
        (finitePTailCoeffTerms kind side l t).2.2 ≤ 3+(l : ℕ) := by sorry







end D1Bound5
end
