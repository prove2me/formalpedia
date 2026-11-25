-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_det_mem
-- name    : Formalism.L2.FormalSeriesBounds.RF.det_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:08.532503+00:00
-- url     : https://prove2.me/theorems/e91748c5-ecda-4524-b98e-74af9a1b1045
-- title:
--   RF: det mem
-- statement:
--   The RF construction uses the det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L32-L37

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.RF.det_mem {R : Type} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (h : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by sorry
