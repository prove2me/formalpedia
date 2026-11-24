-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_glue_fact
-- name    : Formalism.L2.G.Model.TS.glue_fact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:09.575015+00:00
-- url     : https://prove2.me/theorems/8957f52d-e1d9-4fbd-b4c1-a21cdbc5b7c1
-- title:
--   TS: glue fact
-- statement:
--   The TS construction uses the glue fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L124-L129

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

theorem Formalism.L2.G.Model.TS.glue_fact (p : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ x ∈ (glue p).support, (glue p x).factorial = ∏ s, ∏ v ∈ (p s).support, (p s v).factorial := by sorry
