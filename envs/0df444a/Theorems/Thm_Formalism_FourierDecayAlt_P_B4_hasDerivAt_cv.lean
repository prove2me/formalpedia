-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_cv
-- name    : Formalism.FourierDecayAlt.P.B4.hasDerivAt_cv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:27:41.940845+00:00
-- url     : https://prove2.me/theorems/f8a60c12-ba4f-4076-9ff1-d3bf0c317d91
-- title:
--   B4: has Deriv At cv
-- statement:
--   The B4 construction uses the has Deriv At cv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1222-L1234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1222-L1234

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

theorem Formalism.FourierDecayAlt.P.B4.hasDerivAt_cv {H : Mat k r → E} (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Z g : Mat k r}
    (hZ : inLie k r Z) (hg : g ∈ GV k r) (b : Bool) (σ : ℝ) :
    HasDerivAt (fun x : ℝ => H (cv b Z x g)) (op b Z H (cv b Z σ g)) σ := by sorry
