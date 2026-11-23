-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_eq_mul_of_fibers
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.card_eq_mul_of_fibers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:58.260764+00:00
-- url     : https://prove2.me/theorems/e5b6a677-5e76-4d59-b334-a4848835ba46
-- title:
--   Norm Lifting: card eq mul of fibers
-- statement:
--   The Norm Lifting construction uses the card eq mul of fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L18-L42

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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.card_eq_mul_of_fibers {X Y : Type*} [Finite X] (f : X → Y) (c : ℕ)
    (hc : ∀ y, Nat.card {x : X // f x = y} = c) : Nat.card X = c * Nat.card Y := by sorry
