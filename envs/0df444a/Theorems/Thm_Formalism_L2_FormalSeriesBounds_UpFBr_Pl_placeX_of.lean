-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_placeX_of
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.placeX_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:10.436001+00:00
-- url     : https://prove2.me/theorems/7f33a43c-091d-41dc-88d8-9f6577306605
-- title:
--   Pl: place X of
-- statement:
--   The Pl construction uses the place X of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieUpFBrPlP.lean#L318-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieUpFBrPlP.lean#L318-L363

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

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.placeX_of [Module.Free ℤ OE] [Module.Finite ℤ OE] (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R)
    (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) (ε : OE)
    (hε1 : ∃ y, ε * ε - ε = (l : OE) * y) (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) : PlaceX l OE R d em := by sorry
