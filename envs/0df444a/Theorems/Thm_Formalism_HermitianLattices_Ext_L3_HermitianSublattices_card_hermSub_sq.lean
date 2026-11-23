-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_hermSub_sq
-- name    : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_hermSub_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:39.157345+00:00
-- url     : https://prove2.me/theorems/22295a3c-0fff-49d5-87e4-5850196c6aaa
-- title:
--   Hermitian Sublattices: card herm Sub sq
-- statement:
--   The Hermitian Sublattices construction uses the card herm Sub sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L191-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L191-L234

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

theorem Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_hermSub_sq {J : Ideal A} (hJ : ∀ a ∈ J, star a ∈ J) {θ e : A}
    (he : (θ - star θ) * e = 1) : Nat.card (hermSub r J) ^ 2 = Nat.card (entSub r r J) := by sorry
