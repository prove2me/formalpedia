-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cw_eval_tau
-- name    : Formalism.L2.G.Model.TS.cw_eval_tau
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:46.876331+00:00
-- url     : https://prove2.me/theorems/1d7af880-af50-4411-9b89-8d5e016a5538
-- title:
--   TS: cw eval tau
-- statement:
--   The TS construction uses the cw eval tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L225-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L225-L236

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
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
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.L2.G.Model.TS.cw_eval_tau (l : Fin r × Fin r × (Fin r × Fin n)) (y : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_tau l G) = eval (cwUpd l y) G := by sorry
