-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnitaryNormCounts_card_split
-- name    : Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:55.271681+00:00
-- url     : https://prove2.me/theorems/97bd8c4b-66e0-486b-a3ea-5a34d983ae44
-- title:
--   Unitary Norm Counts: card split
-- statement:
--   The Unitary Norm Counts construction uses the card split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardMapEquiv.lean#L138-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardMapEquiv.lean#L138-L205

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardMapEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
open Matrix
variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_split (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} = Nat.card (GL m k) := by sorry
