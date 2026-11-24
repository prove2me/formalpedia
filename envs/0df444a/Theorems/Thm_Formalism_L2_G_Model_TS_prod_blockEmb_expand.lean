-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_prod_blockEmb_expand
-- name    : Formalism.L2.G.Model.TS.prod_blockEmb_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:22.619273+00:00
-- url     : https://prove2.me/theorems/4c3178f9-af88-4985-aa6e-db42092e5214
-- title:
--   TS: prod block Emb expand
-- statement:
--   The TS construction uses the prod block Emb expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L136-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L136-L146

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
variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}

theorem Formalism.L2.G.Model.TS.prod_blockEmb_expand [DecidableEq S] (F : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (F s) = ∑ p ∈ Fintype.piFinset (fun s => (F s).support),
      monomial (glue p) (∏ s, coeff (p s) (F s)) := by sorry
