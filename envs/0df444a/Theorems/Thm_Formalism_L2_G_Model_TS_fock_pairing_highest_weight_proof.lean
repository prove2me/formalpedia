-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_fock_pairing_highest_weight_proof
-- name    : Formalism.L2.G.Model.TS.fock_pairing_highest_weight_proof
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:38.925403+00:00
-- url     : https://prove2.me/theorems/d0eb0d5e-b91b-4d4c-8713-9cf8799b4fd5
-- title:
--   TS: fock pairing highest weight proof
-- statement:
--   The TS construction uses the fock pairing highest weight proof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingHighestWeightProof.lean#L79-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingHighestWeightProof.lean#L79-L122

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingHighestWeightProof
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
open Formalism.GradedWeylDivisibility

theorem Formalism.L2.G.Model.TS.fock_pairing_highest_weight_proof : FockPairingHighestWeight := by sorry
