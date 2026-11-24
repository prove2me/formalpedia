-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_fockR_int_self_pos
-- name    : Formalism.L2.G.Model.TS.fockR_int_self_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:47.229809+00:00
-- url     : https://prove2.me/theorems/322c9761-a8fc-4189-b24d-b98c043e1238
-- title:
--   TS: fock R int self pos
-- statement:
--   The TS construction uses the fock R int self pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L175-L184

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
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

theorem Formalism.L2.G.Model.TS.fockR_int_self_pos {σ : Type*} (f : MvPolynomial σ ℤ) (hf : f ≠ 0) : 0 < fockR f f := by sorry
