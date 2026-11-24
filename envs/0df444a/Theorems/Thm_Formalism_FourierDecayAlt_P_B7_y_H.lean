-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_y_H
-- name    : Formalism.FourierDecayAlt.P.B7.y_H
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:09:38.284123+00:00
-- url     : https://prove2.me/theorems/245084b4-af8d-4f12-81a9-c757bfb78c4c
-- title:
--   B7: y H
-- statement:
--   The B7 construction uses the y H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1643-L1671
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1643-L1671

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

theorem Formalism.FourierDecayAlt.P.B7.y_H (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {G : Mt k r → ℂ} (hG : Integrable G D.μG) :
    Integrable (fun q => ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) *
      ∫ p, G (PhiM D (q, p)) ∂D.μSS) volume ∧
    (∫ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) * ∫ p, G (PhiM D (q, p)) ∂D.μSS) =
      ∫ x, G x ∂D.μG := by sorry
