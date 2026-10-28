-- Prove2me | Theorems.Thm_D1Bound5_fiveRegion_parameters
-- name    : D1Bound5.fiveRegion_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:10.474362+00:00
-- url     : https://prove2.me/theorems/83587f65-d9fa-4732-bbbe-eadb956e5f47
-- title:
--   Five Region parameters
-- statement:
--   Auxiliary result `fiveRegion_parameters` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiveRegionParameters.lean, lines 41-54, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions

section
noncomputable section

namespace D1Bound5
























theorem _root_.D1Bound5.fiveRegion_parameters (r : Fin 5) :
    3 ≤ fiveRegionMinB r ∧ 1 ≤ fiveRegionMinNorm r ∧
    2 < fiveRegionFrontier r ∧ 1 ≤ fiveRegionQ r ∧
    0 < fiveRegionGap r ∧ 0 < fiveRegionCoupledGap r ∧
    0 < fiveRegionPhase r ∧ 0 < fiveRegionPResidual r ∧
    0 < fiveRegionTriangle r ∧
    (51051/400000 : ℝ)*fiveRegionTriangle r/(fiveRegionMinB r)^2 < 1 ∧
    fiveRegionGap r < fiveRegionRetained r/(fiveRegionTriangle r)^2 ∧
    fiveRegionCoupledGap r < fiveRegionRetained r/((3535/409600 : ℝ)*fiveRegionPhase r) ∧
    finitePAdaptiveRate (1/fiveRegionQ r) < fiveRegionPResidual r ∧
    CoupledPhaseRow (fiveRegionQ r) (fiveRegionPhase r) := by sorry



end D1Bound5
end
