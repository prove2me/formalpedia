-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_mem_fixSub
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.mem_fixSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:50.873097+00:00
-- url     : https://prove2.me/theorems/1cf4a3ba-7eb2-411d-8018-47fcab517d46
-- title:
--   Norm Lifting: mem fix Sub
-- statement:
--   The Norm Lifting construction uses the mem fix Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L54-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardFiberMulCardRange.lean#L54-L54

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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.mem_fixSub {w : A} : w ∈ fixSub σ I ↔ w ∈ I ∧ σ w = w := by sorry
