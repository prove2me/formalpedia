-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_opApply_mk
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_mk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:18.966038+00:00
-- url     : https://prove2.me/theorems/4d9ff7be-1862-4fd2-a0e6-fa8510b46690
-- title:
--   Minor Polynomials: op Apply mk
-- statement:
--   The Minor Polynomials construction uses the op Apply mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L87-L97

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_opApply_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable [FiniteDimensional ℂ Wp]

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_mk (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (Lf : FS k r nf)
    (hL : ∀ e ∈ Lf, ∀ X ∈ e.2, inLie k r X) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    opApply (Lf.map (mkTerm D fib)) F g = shape D fib F Lf g := by sorry
