-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_psd_two_cs
-- name    : Formalism.FourierDecayAlt.P.JCx1.decay.psd_two_cs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:02:55.402795+00:00
-- url     : https://prove2.me/theorems/17cae66a-9fef-4fc5-a24b-67ea975aa61e
-- title:
--   decay: psd two cs
-- statement:
--   The decay construction uses the psd two cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L261-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L261-L282

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

theorem Formalism.FourierDecayAlt.P.JCx1.decay.psd_two_cs (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
    ‖M 0 1‖ ^ 2 ≤ (M 0 0).re * (M 1 1).re ∧ 0 ≤ (M 0 0).re ∧ 0 ≤ (M 1 1).re := by sorry
