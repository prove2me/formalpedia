-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cw_foldl_point
-- name    : Formalism.L2.G.Model.TS.cw_foldl_point
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:32.648872+00:00
-- url     : https://prove2.me/theorems/21e2549d-8e7c-425a-85f9-8bc3999b77cf
-- title:
--   TS: cw foldl point
-- statement:
--   The TS construction uses the cw foldl point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L246-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L246-L296

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

theorem Formalism.L2.G.Model.TS.cw_foldl_point (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (h1 : ∀ l ∈ L, l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val)
    (h2 : L.Pairwise fun l l' => l'.1.val ≤ l.1.val ∧ l.2.2 ≠ l'.2.2) :
    L.foldl (fun y l => cwUpd l y) (idFrame (MvPolynomial (Fin r × Fin n) R) r n) =
      fun v => idFrame (MvPolynomial (Fin r × Fin n) R) r n v + if v ∈ L.map (·.2.2) then X v else 0 := by sorry
