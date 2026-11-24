-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_sum_mult
-- name    : Formalism.FourierDecayAlt.P.JCx1.decay.sum_mult
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:44:56.826251+00:00
-- url     : https://prove2.me/theorems/611866e2-dee8-4e9b-8c4e-43cf9ef4a986
-- title:
--   decay: sum mult
-- statement:
--   The decay construction uses the sum mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L214-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L214-L227

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

theorem Formalism.FourierDecayAlt.P.JCx1.decay.sum_mult {Z X : Type} [DecidableEq Z] (P : Finset Z) (F : Z → ℂ) (Y : Finset X) (g : X → Z)
    (hg : ∀ h ∈ Y, g h ∈ P) :
    ∑ p : P, (∑ h ∈ Y, if g h = (p : Z) then (1 : ℂ) else 0) * F p = ∑ h ∈ Y, F (g h) := by sorry
