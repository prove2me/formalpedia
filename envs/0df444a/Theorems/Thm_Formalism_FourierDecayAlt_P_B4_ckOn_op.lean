-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_op
-- name    : Formalism.FourierDecayAlt.P.B4.ckOn_op
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:26:14.252017+00:00
-- url     : https://prove2.me/theorems/d3593f9a-018f-4fee-9f26-9f9ad17ef70e
-- title:
--   B4: ck On op
-- statement:
--   The B4 construction uses the ck On op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L305-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L305-L312

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

theorem Formalism.FourierDecayAlt.P.B4.ckOn_op {f : Mat k r → E} {X : Mat k r} (m : ℕ) (b : Bool)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) (hX : inLie k r X) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) (op b X f) := by sorry
