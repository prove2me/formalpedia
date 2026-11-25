-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsc_zero_weight
-- name    : Formalism.L2.G.Model.TS.tsc_zero_weight
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:24.520386+00:00
-- url     : https://prove2.me/theorems/b8d1685c-95e1-5b3e-98b5-0bd87be4b574
-- title:
--   TS: tsc zero weight
-- statement:
--   The TS construction uses the tsc zero weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/WeylFormNondegenerateGlobal.lean#L165-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/WeylFormNondegenerateGlobal.lean#L165-L188

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_DualWeylIn
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_FinalW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingHighestWeightProof
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_LowerTriangularOverField
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_WeylFormNondegenerateGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

theorem Formalism.L2.G.Model.TS.tsc_zero_weight {O : Type} [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (h0 : ∀ t, ν t = 0) :
    dualWeyl O r n ν ≤ weyl O r n hn ν := by sorry
