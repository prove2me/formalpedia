-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cw_mem_letters
-- name    : Formalism.L2.G.Model.TS.cw_mem_letters
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:58.289026+00:00
-- url     : https://prove2.me/theorems/acb53b9b-00fc-4445-a549-41aa9830866a
-- title:
--   TS: cw mem letters
-- statement:
--   The TS construction uses the cw mem letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L303-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L303-L321

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

theorem Formalism.L2.G.Model.TS.cw_mem_letters (l : Fin r × Fin r × (Fin r × Fin n)) :
    l ∈ cwLetters r n ↔ l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val := by sorry
