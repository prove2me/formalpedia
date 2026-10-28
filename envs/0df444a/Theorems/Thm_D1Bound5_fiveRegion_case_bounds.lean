-- Prove2me | Theorems.Thm_D1Bound5_fiveRegion_case_bounds
-- name    : D1Bound5.fiveRegion_case_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:09:37.074212+00:00
-- url     : https://prove2.me/theorems/b0c07014-3c3c-4898-a8b0-aa6f123a5512
-- title:
--   Five Region case bounds
-- statement:
--   Auxiliary result `fiveRegion_case_bounds` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiveRegionParameters.lean, lines 56-111, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9. Project: https://github.com/tomislav-math/d1-bound5-lean

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
noncomputable section

namespace D1Bound5


























theorem _root_.D1Bound5.fiveRegion_case_bounds (r : Fin 5) (A B : ℝ)
    (hA0 : 0 ≤ A) (hA8 : A^2 ≤ 8) (hc : FiveRegionCase r A B) :
    fiveRegionMinNorm r ≤ A^2 ∧ A ≤ fiveRegionMaxA r ∧
      fiveRegionMinB r ≤ B ∧ 3 ≤ B ∧
      fiveRegionQ r*A ≤ B ∧ A ≤ fiveRegionAnchorRatio r*B := by sorry

end D1Bound5
end
