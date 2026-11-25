-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_l
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_l
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:47.804843+00:00
-- url     : https://prove2.me/theorems/15088ad6-6205-440e-ae7c-92defd2eec5f
-- title:
--   Pl: chi l
-- statement:
--   The Pl construction uses the chi l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L136-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L136-L141

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
variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_l (hl : ((l : ℕ) : R) ∈ maximalIdeal R) (τ : OE →+* R) (s : ℤ_[l] ⊗[ℤ] OE) :
    chi τ (((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * s) = 0 := by sorry
