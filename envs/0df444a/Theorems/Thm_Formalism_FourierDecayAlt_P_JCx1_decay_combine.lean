-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_combine
-- name    : Formalism.FourierDecayAlt.P.JCx1.decay.combine
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:26.206803+00:00
-- url     : https://prove2.me/theorems/c1f66c70-61d2-4137-bf1f-32ecbd7a3aac
-- title:
--   decay: combine
-- statement:
--   The decay construction uses the combine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L374-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L374-L397

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
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)

theorem Formalism.FourierDecayAlt.P.JCx1.decay.combine {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ x a : ι → ℝ) (N M : ℝ)
    (A : Finset ι) (hA : ∀ v, v ∈ A ↔ x v < a v)
    (hL : ∀ v, 0 ≤ abelian₂ v) (hLx : ∀ v, abelian₂ v ≤ x v) (ha : ∀ v, 0 < a v) (hM : 0 ≤ M)
    (h : (∏ v ∈ A, a v ^ K) * N ≤ (∏ v ∈ A, abelian₂ v ^ K) * M) :
    N ≤ (∏ v, min 1 ((x v / a v) ^ K)) * M := by sorry
