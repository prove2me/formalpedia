-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsact_coeff_zero
-- name    : Formalism.L2.G.Model.TS.tsact_coeff_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:47.283658+00:00
-- url     : https://prove2.me/theorems/2b0eb820-d707-4232-b32b-9f4b6b53a401
-- title:
--   TS: tsact coeff zero
-- statement:
--   The TS construction uses the tsact coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L122-L128

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
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

theorem Formalism.L2.G.Model.TS.tsact_coeff_zero (G : Matrix (Fin r) (Fin r) R) (h : MvPolynomial (Fin r × Fin n) R) :
    coeff 0 (rowAct R G h) = coeff 0 h := by sorry
