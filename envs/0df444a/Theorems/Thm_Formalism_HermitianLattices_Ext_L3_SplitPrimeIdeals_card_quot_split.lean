-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_card_quot_split
-- name    : Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_quot_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:26.021829+00:00
-- url     : https://prove2.me/theorems/1aba7f8e-cbbd-472a-ac5b-03e57cf67c89
-- title:
--   Split Prime Ideals: card quot split
-- statement:
--   The Split Prime Ideals construction uses the card quot split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L99-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L99-L111

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

theorem Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_quot_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) :
    Nat.card (A ⧸ P.comap ι) = Nat.card (B ⧸ P) := by sorry
