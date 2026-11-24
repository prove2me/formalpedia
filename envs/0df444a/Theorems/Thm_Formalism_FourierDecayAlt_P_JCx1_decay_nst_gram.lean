-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_nst_gram
-- name    : Formalism.FourierDecayAlt.P.JCx1.decay.nst_gram
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:46:32.865445+00:00
-- url     : https://prove2.me/theorems/7bfef18d-67f5-4e94-8daa-94aba21b9899
-- title:
--   decay: nst gram
-- statement:
--   The decay construction uses the nst gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L342-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L342-L364

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

theorem Formalism.FourierDecayAlt.P.JCx1.decay.nst_gram (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : W)
    (Y : Finset (Pt E)) (T : Finset E) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn (pts Y s T) κ) (t t' : E)
    (ht : t ∈ T) (ht' : t' ∈ T) :
    PairingProductCorollary.PairingGramInequality (D.Nst ε i s w Y (blk κ s t t') t t') (D.Nst ε i s w Y (blk κ s t t) t t).re
      (D.Nst ε i s w Y (blk κ s t' t') t' t').re := by sorry
