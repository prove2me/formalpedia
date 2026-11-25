-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_psd_compress
-- name    : Formalism.FourierDecayAlt.P.JCx1.decay.psd_compress
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:02:51.481702+00:00
-- url     : https://prove2.me/theorems/9726d63a-c5b1-4cf2-8e8e-bcc67f8014dd
-- title:
--   decay: psd compress
-- statement:
--   The decay construction uses the psd compress property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L229-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L229-L254

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay

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
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder

theorem Formalism.FourierDecayAlt.P.JCx1.decay.psd_compress {Z X J : Type} [Fintype J] [DecidableEq Z] (P : Finset Z) (H : Z → Z → ℂ)
    (hH : PSDOn P H) (Y : J → Finset X) (g : J → X → Z) (hg : ∀ j, ∀ h ∈ Y j, g j h ∈ P) :
    Matrix.PosSemidef (Matrix.of fun j k : J => ∑ h ∈ Y j, ∑ h' ∈ Y k, H (g j h) (g k h')) := by sorry
