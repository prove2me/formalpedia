-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_linPart_apply
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.linPart_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:46.598515+00:00
-- url     : https://prove2.me/theorems/9e4c1309-3c12-4d4d-a687-9cf803f4dfca
-- title:
--   Norm Lifting: lin Part apply
-- statement:
--   The Norm Lifting construction uses the lin Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L139-L140

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
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.linPart_apply (I : Ideal A) {M : ℕ} (y : Fin M → A) (δ : Fin M → I) :
    linPart σ I y δ = ∑ i, (σ (y i) * (δ i : A) + σ (δ i) * y i) := by sorry
