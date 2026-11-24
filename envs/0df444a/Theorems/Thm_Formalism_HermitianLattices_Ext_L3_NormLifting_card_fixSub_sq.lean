-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_fixSub_sq
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.card_fixSub_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:38.519788+00:00
-- url     : https://prove2.me/theorems/0467edfb-5fce-48b2-9093-b63602b7b0c2
-- title:
--   Norm Lifting: card fix Sub sq
-- statement:
--   The Norm Lifting construction uses the card fix Sub sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L96-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L96-L125

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)
variable {σ I}

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.card_fixSub_sq (hσ : ∀ a, σ (σ a) = a) (hI : ∀ a ∈ I, σ a ∈ I) {θ e : A}
    (he : (θ - σ θ) * e = 1) : Nat.card (fixSub σ I) ^ 2 = Nat.card I := by sorry
