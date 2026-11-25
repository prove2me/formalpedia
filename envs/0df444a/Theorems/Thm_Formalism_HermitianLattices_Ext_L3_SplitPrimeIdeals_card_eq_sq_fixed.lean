-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_card_eq_sq_fixed
-- name    : Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_eq_sq_fixed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:23.000945+00:00
-- url     : https://prove2.me/theorems/802c1145-2e24-4c1b-a195-6f9d497943ad
-- title:
--   Split Prime Ideals: card eq sq fixed
-- statement:
--   The Split Prime Ideals construction uses the card eq sq fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L6-L8

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

theorem Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_eq_sq_fixed {k : Type*} [Field k] (τ : k →+* k) (hτ : ∀ x, τ (τ x) = x) (θ : k)
    (hθ : θ - τ θ ≠ 0) : Nat.card k = Nat.card {x : k // τ x = x} ^ 2 := by sorry
