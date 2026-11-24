-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cw_wordOf
-- name    : Formalism.L2.G.Model.TS.cw_wordOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:44.084621+00:00
-- url     : https://prove2.me/theorems/791f4c7e-378a-4068-a3d0-9f9a3df68949
-- title:
--   TS: cw word Of
-- statement:
--   The TS construction uses the cw word Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L355-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L355-L364

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

theorem Formalism.L2.G.Model.TS.cw_wordOf (e : Fin r × Fin n →₀ ℕ) :
    wordOf e = (cwLetters r n).map fun l => (l.1, l.2.1, e l.2.2) := by sorry
