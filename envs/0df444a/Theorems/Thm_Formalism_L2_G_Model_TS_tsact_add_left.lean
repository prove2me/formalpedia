-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsact_add_left
-- name    : Formalism.L2.G.Model.TS.tsact_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:20.272512+00:00
-- url     : https://prove2.me/theorems/cb3264ce-1ea9-45a4-a0ef-8a9d577c4138
-- title:
--   TS: tsact add left
-- statement:
--   The TS construction uses the tsact add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L28-L35

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
variable {σ R : Type*} [CommRing R]

theorem Formalism.L2.G.Model.TS.tsact_add_left (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by sorry
