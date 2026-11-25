-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_natCast_mul_tmul
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.natCast_mul_tmul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:57.613359+00:00
-- url     : https://prove2.me/theorems/2d15857e-c9d8-42d7-a21b-0edbcf7888ec
-- title:
--   Pl: nat Cast mul tmul
-- statement:
--   The Pl construction uses the nat Cast mul tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L30-L32

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

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.natCast_mul_tmul (k : ℕ) (z : ℤ_[l]) (y : OE) :
    ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (z ⊗ₜ y) = ((k : ℤ_[l]) * z) ⊗ₜ y := by sorry
