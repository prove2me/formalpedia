-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_uniform
-- name    : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_uniform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:58.36023+00:00
-- url     : https://prove2.me/theorems/f269e43b-f523-4b49-be39-508a69441140
-- title:
--   Hermitian Sublattices: card uniform
-- statement:
--   The Hermitian Sublattices construction uses the card uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L55-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L55-L93

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
variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z]

theorem Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_uniform [Finite A] (B : AddSubgroup A) (Z' : AddSubgroup Z) (g : A → Z) (p : A → Prop)
    (hp : ∀ a, ∀ b ∈ B, (p (a + b) ↔ p a))
    (hφ : ∀ a, p a → g a ∈ Z' → ∃ φ : B →+ Z, (∀ b : B, g (a + b) = g a + φ b) ∧
      ∀ z ∈ Z', ∃ b, φ b = z) :
    Nat.card {a // p a ∧ g a ∈ Z'} = Nat.card {a // p a ∧ g a = 0} * Nat.card Z' := by sorry
