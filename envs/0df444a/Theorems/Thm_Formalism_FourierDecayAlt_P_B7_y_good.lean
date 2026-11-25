-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_y_good
-- name    : Formalism.FourierDecayAlt.P.B7.y_good
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:09:12.744018+00:00
-- url     : https://prove2.me/theorems/9921bf55-48a6-4163-9c53-27deb226ad2a
-- title:
--   B7: y good
-- statement:
--   The B7 construction uses the y good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1689-L1705
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1689-L1705

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
attribute [local instance] sfNu

theorem Formalism.FourierDecayAlt.P.B7.y_good (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) (hC : ConjInv D) {A : ℝ} (hCC : CCIntegrable D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∀ᵐ q : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 ∨
      (Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 * ‖hsL (JM D F τ q)‖ ^ 2) volume ∧
        ((∫ τ : ℝ × ℝ, w₁ τ.1 * w₂ τ.2 * ‖hsL (JM D F τ q)‖ ^ 2 : ℝ) : ℂ) =
          ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS) := by sorry
