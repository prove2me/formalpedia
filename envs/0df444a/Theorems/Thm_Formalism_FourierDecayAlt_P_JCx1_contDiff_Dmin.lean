-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_Dmin
-- name    : Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:23.877532+00:00
-- url     : https://prove2.me/theorems/d3b38597-c699-4161-aac6-1f43ba61c1af
-- title:
--   JCx1: cont Diff Dmin
-- statement:
--   The JCx1 construction uses the cont Diff Dmin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L120-L123

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

theorem Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Dmin k r z z' g l) := by sorry
