-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_integrable
-- name    : Formalism.FourierDecayAlt.P.B5.hs_integrable
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:01:56.758195+00:00
-- url     : https://prove2.me/theorems/275e4928-f774-49eb-b960-eb39768dabcc
-- title:
--   B5: hs integrable
-- statement:
--   The B5 construction uses the hs integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L663-L672
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L663-L672

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.B5.hs_integrable (D : RealPlaceData k r Wp Wq) {A B : Mat k r → (Wq →L[ℂ] Wp)}
    (hA : ContinuousOn A (GV k r)) (hB : ContinuousOn B (GV k r))
    (h : Integrable (fun g : Mt k r => ‖B (Matrix.of g)‖ * ‖A (Matrix.of g)‖) D.μG) :
    Integrable (fun g : Mt k r => hsInner (A (Matrix.of g)) (B (Matrix.of g))) D.μG := by sorry
