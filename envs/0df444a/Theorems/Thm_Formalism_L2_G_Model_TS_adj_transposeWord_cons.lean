-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_adj_transposeWord_cons
-- name    : Formalism.L2.G.Model.TS.adj_transposeWord_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:16.461407+00:00
-- url     : https://prove2.me/theorems/f5032dbf-23f8-43ee-9df6-55d05c4a8539
-- title:
--   TS: adj transpose Word cons
-- statement:
--   The TS construction uses the adj transpose Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingDividedAdjoint.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingDividedAdjoint.lean#L108-L110

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
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

theorem Formalism.L2.G.Model.TS.adj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by sorry
