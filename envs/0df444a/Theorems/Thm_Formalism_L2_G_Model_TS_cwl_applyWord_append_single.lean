-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cwl_applyWord_append_single
-- name    : Formalism.L2.G.Model.TS.cwl_applyWord_append_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:50.048817+00:00
-- url     : https://prove2.me/theorems/d6116650-0a0c-4869-83b0-be4337e87056
-- title:
--   TS: cwl apply Word append single
-- statement:
--   The TS construction uses the cwl apply Word append single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L120-L123

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

theorem Formalism.L2.G.Model.TS.cwl_applyWord_append_single (w : List (Fin r × Fin r × ℕ)) (x : Fin r × Fin r × ℕ)
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (w ++ [x]) F = applyWord R w (rowDiv R x.1 x.2.1 x.2.2 F) := by sorry
