-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_fixq
-- name    : Formalism.FourierDecayAlt.P.B7.w_fixq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:11:43.417559+00:00
-- url     : https://prove2.me/theorems/99a7c8b6-1918-448b-b22b-0fbbffc4995e
-- title:
--   B7: w fixq
-- statement:
--   The B7 construction uses the w fixq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1540-L1568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1540-L1568

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD

theorem Formalism.FourierDecayAlt.P.B7.w_fixq (D : RealPlaceData k r Wp Wq) (hC : ConjInv D) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ContinuousOn F (GV k r)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D)
    (hint : Integrable (fun p => rho D p F (gq D q)) D.μSS) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2) volume ∧
    (((∫ τ : ℝ × ℝ, w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS := by sorry
