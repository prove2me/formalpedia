-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsact_rowAct_X
-- name    : Formalism.L2.G.Model.TS.tsact_rowAct_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:08.30481+00:00
-- url     : https://prove2.me/theorems/cd013cf9-f6eb-47fb-8c49-2279190d1ff1
-- title:
--   TS: tsact row Act X
-- statement:
--   The TS construction uses the tsact row Act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L118-L120

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

theorem Formalism.L2.G.Model.TS.tsact_rowAct_X (G : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R G (X v) = ∑ b : Fin r, C (G v.1 b) * X (b, v.2) := by sorry
