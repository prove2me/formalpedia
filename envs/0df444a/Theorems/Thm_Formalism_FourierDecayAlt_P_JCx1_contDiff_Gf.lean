-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_Gf
-- name    : Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:38.431686+00:00
-- url     : https://prove2.me/theorems/843dfd02-ff99-4f4f-a1d7-8ee2c3ce2183
-- title:
--   JCx1: cont Diff Gf
-- statement:
--   The JCx1 construction uses the cont Diff Gf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L133-L137

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

theorem Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Gf k r z z' g) := by sorry
