-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_adM_cont
-- name    : Formalism.FourierDecayAlt.P.JFxDs3.adM_cont
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:32:19.366325+00:00
-- url     : https://prove2.me/theorems/7153137b-71a9-4081-ba06-2c96bbe8521c
-- title:
--   JFx Ds3: ad M cont
-- statement:
--   The JFx Ds3 construction uses the ad M cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L192-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L192-L215

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.JFxDs3.adM_cont (D : RealPlaceData k r Wp Wq) (x : Bool × Mat k r) :
    ContinuousOn (fun p => (adM p x).2) {p : SS k r | D.inSS p} := by sorry
