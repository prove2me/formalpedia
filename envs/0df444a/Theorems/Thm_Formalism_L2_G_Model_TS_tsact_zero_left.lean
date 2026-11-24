-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsact_zero_left
-- name    : Formalism.L2.G.Model.TS.tsact_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:53.0025+00:00
-- url     : https://prove2.me/theorems/2ec478e4-5fab-4a6d-b479-3b26238cf8c5
-- title:
--   TS: tsact zero left
-- statement:
--   The TS construction uses the tsact zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L45-L47

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

theorem Formalism.L2.G.Model.TS.tsact_zero_left (g : MvPolynomial σ R) : fockR (0 : MvPolynomial σ R) g = 0 := by sorry
