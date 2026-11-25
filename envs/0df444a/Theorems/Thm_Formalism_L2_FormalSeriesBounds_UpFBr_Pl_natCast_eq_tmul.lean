-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_natCast_eq_tmul
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.natCast_eq_tmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:57.634284+00:00
-- url     : https://prove2.me/theorems/a907b2e5-b82a-4e60-bef0-1a48e45214bc
-- title:
--   Pl: nat Cast eq tmul
-- statement:
--   The Pl construction uses the nat Cast eq tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L20-L23

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.natCast_eq_tmul (k : ℕ) : ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) = (k : ℤ_[l]) ⊗ₜ (1 : OE) := by sorry
