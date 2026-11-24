-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_lowerTri_of_interlaced
-- name    : Formalism.L2.G.Model.TS.lowerTri_of_interlaced
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:54.001853+00:00
-- url     : https://prove2.me/theorems/4cdd0a3f-ab6a-4bef-a552-28e4e47e6bae
-- title:
--   TS: lower Tri of interlaced
-- statement:
--   The TS construction uses the lower Tri of interlaced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/LowerTriangularOverField.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/LowerTriangularOverField.lean#L13-L35

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCassemLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_LowerTriangularOverField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem Formalism.L2.G.Model.TS.lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by sorry
