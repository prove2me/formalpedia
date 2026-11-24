-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_det
-- name    : Formalism.FourierDecayAlt.P.JCx1.contDiff_det
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:46:30.750028+00:00
-- url     : https://prove2.me/theorems/151a948c-f26f-4c7d-8059-c3401a4ba9fb
-- title:
--   JCx1: cont Diff det
-- statement:
--   The JCx1 construction uses the cont Diff det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L105-L111

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.JCx1.contDiff_det {n : Type} [Fintype n] [DecidableEq n] {k r : ℕ} (M : B.Mat k r → Matrix n n ℂ)
    (hM : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun g => M g a b)) : ContDiff ℝ (⊤ : ℕ∞) (fun g => (M g).det) := by sorry
