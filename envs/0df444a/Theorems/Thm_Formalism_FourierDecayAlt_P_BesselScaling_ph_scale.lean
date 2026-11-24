-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BesselScaling_ph_scale
-- name    : Formalism.FourierDecayAlt.P.BesselScaling.ph_scale
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:50.815829+00:00
-- url     : https://prove2.me/theorems/3d230640-057a-48a8-9b2b-be7da76fc643
-- title:
--   Bessel Scaling: ph scale
-- statement:
--   The Bessel Scaling construction uses the ph scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselScaling.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselScaling.lean#L51-L56

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BesselScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
variable [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.BesselScaling.ph_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Ph (scaleG D c hc) F F' p = ((c : ℝ) : ℂ) * Ph D F F' p := by sorry
