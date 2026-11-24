-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_add
-- name    : Formalism.L2.G.Model.TS.cwl_coeffT_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:10.278166+00:00
-- url     : https://prove2.me/theorems/b7327772-c892-40c7-8450-4e8422feb333
-- title:
--   TS: cwl coeff T add
-- statement:
--   The TS construction uses the cwl coeff T add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L37-L41

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

theorem Formalism.L2.G.Model.TS.cwl_coeffT_add (d : Fin r × Fin n →₀ ℕ)
    (G H : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_coeffT d (G + H) = cwl_coeffT d G + cwl_coeffT d H := by sorry
