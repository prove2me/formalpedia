-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_formula
-- name    : Formalism.FourierDecayAlt.P.B7.jc_formula
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:07:27.816361+00:00
-- url     : https://prove2.me/theorems/35e6594e-cdb4-421a-be5b-53642c3a6fe3
-- title:
--   B7: jc formula
-- statement:
--   The B7 construction uses the jc formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L820-L833
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L820-L833

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

theorem Formalism.FourierDecayAlt.P.B7.jc_formula (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ContinuousOn F (GV k r)) :
    (∫⁻ g, ‖FM F g‖ₑ ∂D.μG) = ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) * jc_E D F q := by sorry
