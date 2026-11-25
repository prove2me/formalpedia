-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_weylPair_of
-- name    : Formalism.L2.G.Model.TS.weylPair_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:15.582738+00:00
-- url     : https://prove2.me/theorems/bdddab0f-5de8-459b-b7c9-8047832788eb
-- title:
--   TS: weyl Pair of
-- statement:
--   The TS construction uses the weyl Pair of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/WeylFormNondegenerateGlobal.lean#L102-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/WeylFormNondegenerateGlobal.lean#L102-L123

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

theorem Formalism.L2.G.Model.TS.weylPair_of (hB : FockRBilin) (hA : FockRWordAdj) (hH : FockPairingHighestWeight) : WeylPair := by sorry
