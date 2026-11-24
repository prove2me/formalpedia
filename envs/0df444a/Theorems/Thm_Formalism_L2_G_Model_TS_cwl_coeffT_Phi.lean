-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_Phi
-- name    : Formalism.L2.G.Model.TS.cwl_coeffT_Phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:16.699608+00:00
-- url     : https://prove2.me/theorems/2dfb8371-36ce-4b26-8beb-b5c95540f1f5
-- title:
--   TS: cwl coeff T Phi
-- statement:
--   The TS construction uses the cwl coeff T Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L134-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L134-L207

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

theorem Formalism.L2.G.Model.TS.cwl_coeffT_Phi (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hL : (L.map (·.2.2)).Nodup) (F : MvPolynomial (Fin r × Fin n) R) (d : Fin r × Fin n →₀ ℕ) :
    cwl_coeffT d (cwl_Phi L (cwl_iota F)) =
      if (∀ u, u ∉ L.map (·.2.2) → d u = 0) then
        applyWord R (L.map fun l => (l.1, l.2.1, d l.2.2)) F else 0 := by sorry
