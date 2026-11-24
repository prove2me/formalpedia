-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_range_trI
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.range_trI
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:18.008808+00:00
-- url     : https://prove2.me/theorems/b9d78139-94c6-4d91-b9e9-dc4ab8bddd67
-- title:
--   Norm Lifting: range tr I
-- statement:
--   The Norm Lifting construction uses the range tr I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L82-L94

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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.range_trI (hσ : ∀ a, σ (σ a) = a) (hI : ∀ a ∈ I, σ a ∈ I) {θ e : A}
    (he : (θ - σ θ) * e = 1) : (trI σ I).range = fixSub σ I := by sorry
