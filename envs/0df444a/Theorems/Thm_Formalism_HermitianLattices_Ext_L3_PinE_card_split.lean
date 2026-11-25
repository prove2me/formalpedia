-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinE_card_split
-- name    : Formalism.HermitianLattices.Ext.L3.PinE.card_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:13.324569+00:00
-- url     : https://prove2.me/theorems/d81fe17e-5cef-4c91-9702-257b0e72f4b2
-- title:
--   Pin E: card split
-- statement:
--   The Pin E construction uses the card split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L58-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L58-L129

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem Formalism.HermitianLattices.Ext.L3.PinE.card_split [Finite A] (H' : Matrix κ κ A)
    (htr : ∀ x : Unit ⊕ κ → A, star x ⬝ᵥ (HH H' *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A, Gᴴ * HH H' * G = HH H' ∧ G * G' = 1 ∧ G *ᵥ e₀ = x) :
    Nat.card {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} =
      Nat.card {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} *
        Nat.card {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} := by sorry
