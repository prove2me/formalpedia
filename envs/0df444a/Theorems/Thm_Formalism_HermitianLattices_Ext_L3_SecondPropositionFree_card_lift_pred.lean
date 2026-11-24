-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SecondPropositionFree_card_lift_pred
-- name    : Formalism.HermitianLattices.Ext.L3.SecondPropositionFree.card_lift_pred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:17.556187+00:00
-- url     : https://prove2.me/theorems/0b4f2691-7d64-49f8-8a05-8b20ba11928f
-- title:
--   Second Proposition Free: card lift pred
-- statement:
--   The Second Proposition Free construction uses the card lift pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemRangeLinPart.lean#L10-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemRangeLinPart.lean#L10-L166

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemRangeLinPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
open NormLifting
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

theorem Formalism.HermitianLattices.Ext.L3.SecondPropositionFree.card_lift_pred [Finite A] (hπ : Function.Surjective π) (hστ : ∀ a, π (σ a) = τ (π a))
    (hσ : ∀ a, σ (σ a) = a) (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0) {θ e : A}
    (he : (θ - σ θ) * e = 1) {n : A} (hn : σ n = n) (q : ℕ)
    (hq : Nat.card A = q ^ 2 * Nat.card B) (M : ℕ) (hM : 1 ≤ M) (p : (Fin M → B) → Prop)
    (hsurj : ∀ y : Fin M → A, p (fun i => π (y i)) → ∀ w ∈ fixSub σ (RingHom.ker π),
      w ∈ (linPart σ (RingHom.ker π) y).range) :
    Nat.card {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =
      q ^ (2 * M - 1) * Nat.card {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n} := by sorry
