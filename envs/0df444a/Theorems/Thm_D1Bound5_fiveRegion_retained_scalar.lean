-- Prove2me | Theorems.Thm_D1Bound5_fiveRegion_retained_scalar
-- name    : D1Bound5.fiveRegion_retained_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:22.943457+00:00
-- url     : https://prove2.me/theorems/419b132a-832f-43c6-ad9b-58ec79aae1e4
-- title:
--   Five Region retained scalar
-- statement:
--   Scalar use of the actual H48 retained estimate. The phase bound is kept coupled to the relabeled residual throughout. This intermediate lemma is subsequently supplied with the tuple's actual analytic data.
-- source:
--   D1Bound5/FiveRegionRetainedScalar.lean, lines 5-88, SHA-256 59bcf0db3c2678216f6fff40f758e9c54d8c383f3da2ef452f68334764d2fe57. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.fiveRegion_retained_scalar (r : Fin 5) (A B S T C R Phi : ℝ)
    (hA : 1 ≤ A) (hBm : fiveRegionMinB r ≤ B) (hBS : B ≤ S)
    (hR : 0 < R) (hRQ : R ≤ fiveRegionTriangle r) (hPhi : 0 ≤ Phi)
    (hphase : R^2*Phi < fiveRegionPhase r)
    (hfront : fiveRegionFrontier r*A*B*S < T)
    (hret : (9999/10000 : ℝ)*(200/19)^2*
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(A^2*T^5/S^2) < C) :
    fiveRegionGap r*(A^7*B^5*S^3) < C ∧
    (fiveRegionCoupledGap r*((3535/409600 : ℝ)*Phi))*(A^7*B^5*S^3) < C := by sorry

end D1Bound5
end
