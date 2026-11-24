-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_mkTerm_word
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.mkTerm_word
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:20.913453+00:00
-- url     : https://prove2.me/theorems/4064ed68-c7b1-4e9c-877a-5c112f9f5962
-- title:
--   Minor Polynomials: mk Term word
-- statement:
--   The Minor Polynomials construction uses the mk Term word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L82-L85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mkTerm_word

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.mkTerm_word (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    {e : CT k r nf × List (Mat k r)} (h : ∀ X ∈ e.2, inLie k r X) : (mkTerm D fib e).word = e.2 := by sorry
