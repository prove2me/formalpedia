-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_monoM_eq
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.monoM_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:23.524535+00:00
-- url     : https://prove2.me/theorems/4b0eafc1-cbf9-4985-ae30-155c456ed5a1
-- title:
--   Minor Polynomials: mono M eq
-- statement:
--   The Minor Polynomials construction uses the mono M eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtCvs.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtCvs.lean#L20-L21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.monoM_eq (D : RealPlaceData k r Wp Wq) (a b : Fin (r + 2) → ℕ) (c : ℕ) (g : Mat k r) :
    C6.monoM D a b c g = (∏ l, fct D.z D.z' a b g l) * ((Gf k r D.z D.z' g : ℝ) : ℂ)⁻¹ ^ c := by sorry
