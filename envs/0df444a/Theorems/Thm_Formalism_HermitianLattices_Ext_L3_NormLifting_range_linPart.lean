-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_range_linPart
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.range_linPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:11.862599+00:00
-- url     : https://prove2.me/theorems/7b45b349-33df-43af-840f-070b253ece56
-- title:
--   Norm Lifting: range lin Part
-- statement:
--   The Norm Lifting construction uses the range lin Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L142-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L142-L177

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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.range_linPart (hσ : ∀ a, σ (σ a) = a) {I : Ideal A} (hI : ∀ a ∈ I, σ a ∈ I)
    (hsq : ∀ a ∈ I, ∀ b ∈ I, a * b = 0) {θ e : A} (he : (θ - σ θ) * e = 1) {n m : A}
    (hnm : n * m = 1) {M : ℕ} (y : Fin M → A) (hy : n - ∑ i, σ (y i) * y i ∈ I) :
    (linPart σ I y).range = fixSub σ I := by sorry
