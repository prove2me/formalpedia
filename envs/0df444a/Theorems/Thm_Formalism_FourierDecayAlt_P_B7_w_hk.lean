-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_hk
-- name    : Formalism.FourierDecayAlt.P.B7.w_hk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:09:24.226284+00:00
-- url     : https://prove2.me/theorems/80bc230e-0892-498c-9083-3a8d5f3127ae
-- title:
--   B7: w hk
-- statement:
--   The B7 construction uses the w hk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1475-L1482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L1475-L1482

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

theorem Formalism.FourierDecayAlt.P.B7.w_hk (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D)
    (p p' : SS k r) (hp : D.inSS p) (hp' : D.inSS p') :
    inner ℂ (hsVec (rho D p F (gq D q))) (hsVec (rho D (tr p p') F (gq D q))) = KM D F p' (PhiM D (q, p)) := by sorry
