-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_inj
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_inj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:29.441981+00:00
-- url     : https://prove2.me/theorems/bdb78a25-923f-4998-9741-1e7c0e36c104
-- title:
--   Pl: chi inj
-- statement:
--   The Pl construction uses the chi inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieUpFBrPlP.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieUpFBrPlP.lean#L95-L108

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
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
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_inj (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) :
    Function.Injective fun a => chi (l := l) (em a) := by sorry
