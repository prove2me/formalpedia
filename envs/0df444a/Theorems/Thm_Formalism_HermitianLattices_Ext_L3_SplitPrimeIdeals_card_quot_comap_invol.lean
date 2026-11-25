-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_card_quot_comap_invol
-- name    : Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_quot_comap_invol
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:22.167817+00:00
-- url     : https://prove2.me/theorems/cdc2344f-2f36-43c5-86df-02e7d6883313
-- title:
--   Split Prime Ideals: card quot comap invol
-- statement:
--   The Split Prime Ideals construction uses the card quot comap invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L30-L35

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
variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

theorem Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_quot_comap_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) :
    Nat.card (B ⧸ P.comap σ) = Nat.card (B ⧸ P) := by sorry
