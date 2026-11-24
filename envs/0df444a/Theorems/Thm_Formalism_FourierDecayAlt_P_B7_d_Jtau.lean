-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_Jtau
-- name    : Formalism.FourierDecayAlt.P.B7.d_Jtau
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:05:09.378176+00:00
-- url     : https://prove2.me/theorems/733fab2d-5c60-49dd-816d-30e7156f7784
-- title:
--   B7: d Jtau
-- statement:
--   The B7 construction uses the d Jtau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L608-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L608-L627

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
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.B7.d_Jtau (D : RealPlaceData k r Wp Wq) (hJ : DilJac D) (τ t : ℝ × ℝ) (h1 : 0 < t.1) (h2 : 0 < t.2)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    Jtau D τ (dilF t F) g = ((t.1 * t.2) ^ kap k r : ℝ) •
      Jtau D (τ.1 * t.1, τ.2 * t.2) F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) := by sorry
