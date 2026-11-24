-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsact_chain
-- name    : Formalism.L2.G.Model.TS.tsact_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:05.972534+00:00
-- url     : https://prove2.me/theorems/0c8269cb-96bf-4235-82f8-395fb46e76d2
-- title:
--   TS: tsact chain
-- statement:
--   The TS construction uses the tsact chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L130-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L130-L156

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

theorem Formalism.L2.G.Model.TS.tsact_chain (G : Matrix (Fin r) (Fin r) R) (b : Fin r) (s : Fin n) (h : MvPolynomial (Fin r × Fin n) R) :
    pderiv (b, s) (rowAct R G h) = ∑ a : Fin r, G a b • rowAct R G (pderiv (a, s) h) := by sorry
