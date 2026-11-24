-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_lift_matrix
-- name    : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_lift_matrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:46.980106+00:00
-- url     : https://prove2.me/theorems/83f7c6a3-7aa6-4cb6-ba85-c61ae06b1591
-- title:
--   Hermitian Sublattices: card lift matrix
-- statement:
--   The Hermitian Sublattices construction uses the card lift matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L247-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L247-L336

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

theorem Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_lift_matrix [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a)) (𝔟 : Ideal A) (h𝔟s : ∀ a ∈ 𝔟, star a ∈ 𝔟)
    (h𝔟2 : ∀ a ∈ 𝔟, ∀ b ∈ 𝔟, a * b = 0) (H : Matrix m m A) (hH : Hᴴ = H) (T : Matrix r r A)
    (hT : Tᴴ = T) (p' : Matrix m r A' → Prop)
    (hinv : ∀ X Y : Matrix m r A, Y ∈ entSub m r 𝔟 → (p' ((X + Y).map π) ↔ p' (X.map π)))
    (RC : ∀ X : Matrix m r A, p' (X.map π) → (∀ i j, (Xᴴ * H * X - T) i j ∈ RingHom.ker π) →
      ∀ S ∈ hermSub r (RingHom.ker π), ∃ Y ∈ entSub m r 𝔟, Xᴴ * H * Y + Yᴴ * H * X = S) :
    Nat.card {X : Matrix m r A // p' (X.map π) ∧ Xᴴ * H * X = T} *
        Nat.card (hermSub r (RingHom.ker π)) =
      Nat.card (entSub m r (RingHom.ker π)) *
        Nat.card {X' : Matrix m r A' // p' X' ∧ X'ᴴ * (H.map π) * X' = T.map π} := by sorry
