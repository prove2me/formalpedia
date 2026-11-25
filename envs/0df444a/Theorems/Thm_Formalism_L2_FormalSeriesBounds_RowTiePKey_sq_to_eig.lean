-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePKey_sq_to_eig
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePKey.sq_to_eig
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:50.005392+00:00
-- url     : https://prove2.me/theorems/ebccca9b-cae4-4de1-bc1d-229853633e53
-- title:
--   Row Tie PKey: sq to eig
-- statement:
--   The Row Tie PKey construction uses the sq to eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePKeyJoint.lean#L11-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePKeyJoint.lean#L11-L56

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJointDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePKey
variable {C : Type} [Field C] [CharZero C] {n : ℕ}

theorem Formalism.L2.FormalSeriesBounds.RowTiePKey.sq_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (u : Fin n → C)
    (h2 : Matrix.mulVec t (Matrix.mulVec t u - μ • u) = μ • (Matrix.mulVec t u - μ • u)) :
    Matrix.mulVec t u = μ • u := by sorry
