-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_lint_KM_le
-- name    : Formalism.FourierDecayAlt.P.B7.u_lint_KM_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:06.625077+00:00
-- url     : https://prove2.me/theorems/0609cbeb-f866-4bf0-8b32-766134c894c5
-- title:
--   B7: u lint KM le
-- statement:
--   The B7 construction uses the u lint KM le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1190-L1218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1190-L1218

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

theorem Formalism.FourierDecayAlt.P.B7.u_lint_KM_le (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ p, D.inSS p → (∫⁻ x, ‖KM D F p x‖ₑ ∂D.μG) ≤
      K * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by sorry
