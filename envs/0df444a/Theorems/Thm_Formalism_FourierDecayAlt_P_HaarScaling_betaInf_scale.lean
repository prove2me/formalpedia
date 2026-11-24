-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HaarScaling_betaInf_scale
-- name    : Formalism.FourierDecayAlt.P.HaarScaling.betaInf_scale
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:47.375537+00:00
-- url     : https://prove2.me/theorems/ddca4bfd-1960-4f37-9c57-bcdbb81dc5a0
-- title:
--   Haar Scaling: beta Inf scale
-- statement:
--   The Haar Scaling construction uses the beta Inf scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L65-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L65-L83

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
variable [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.HaarScaling.betaInf_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by sorry
