-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsc_coeff_pair
-- name    : Formalism.L2.G.Model.TS.tsc_coeff_pair
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:41:02.314357+00:00
-- url     : https://prove2.me/theorems/0698d25c-ea57-544b-b1d6-eca44a23feaa
-- title:
--   TS: tsc coeff pair
-- statement:
--   The TS construction uses the tsc coeff pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/WeylFormNondegenerateGlobal.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/WeylFormNondegenerateGlobal.lean#L89-L100

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

theorem Formalism.L2.G.Model.TS.tsc_coeff_pair (hA : FockRWordAdj) (hH : FockPairingHighestWeight) (hC : CoeffWord) {K : Type} [Field K] [CharZero K] {r n : ℕ}
    (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (Q : MvPolynomial (Fin r × Fin n) K) (hQ : Q ∈ dualWeyl K r n ν)
    (e : Fin r × Fin n →₀ ℕ) (he : LowerTri e) :
    coeff e Q = 0 ∨ fockR (applyWord K (transposeWord (wordOf e)) (hw K hn ν)) Q =
      coeff e Q * fockR (hw K hn ν) (hw K hn ν) := by sorry
