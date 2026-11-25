-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_alg
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_alg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:36:03.379962+00:00
-- url     : https://prove2.me/theorems/ad7a440c-c062-4d52-9fb4-1cd0c529d814
-- title:
--   Pl: chi alg
-- statement:
--   The Pl construction uses the chi alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean#L143-L146

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

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_alg (τ : OE →+* R) (r : ℤ_[l]) :
    chi τ (algebraMap ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) r) = ((residue R).comp (algebraMap ℤ_[l] R)) r := by sorry
