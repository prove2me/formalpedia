-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_ext
-- name    : Formalism.FourierDecayAlt.P.B4.hasDerivAt_ext
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:57.297479+00:00
-- url     : https://prove2.me/theorems/2f96de98-ced6-4c35-80af-44a5d55382e2
-- title:
--   B4: has Deriv At ext
-- statement:
--   The B4 construction uses the has Deriv At ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L251-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L251-L269

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.B4.hasDerivAt_ext {f f' : Mat k r → E} {U : Set (Mat k r)} {g X : Mat k r} (b : Bool)
    (hU : IsOpen U) (hg : g ∈ U) (hgG : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (cv b X t g)) (fderiv ℝ f' g (vf b X g)) 0 := by sorry
