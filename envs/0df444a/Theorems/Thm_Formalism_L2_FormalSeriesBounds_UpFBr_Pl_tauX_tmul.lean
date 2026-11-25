-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_tauX_tmul
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.tauX_tmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:36:11.094195+00:00
-- url     : https://prove2.me/theorems/45401995-5d3f-4e1b-8190-204ad09abadc
-- title:
--   Pl: tau X tmul
-- statement:
--   The Pl construction uses the tau X tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L16-L18

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

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.tauX_tmul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) (z : ℤ_[l]) (x : OE) :
    tauX τ (z ⊗ₜ x) = algebraMap ℤ_[l] R z * τ x := by sorry
