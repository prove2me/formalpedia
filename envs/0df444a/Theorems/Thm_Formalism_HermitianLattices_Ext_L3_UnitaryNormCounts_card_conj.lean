-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnitaryNormCounts_card_conj
-- name    : Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:16.076839+00:00
-- url     : https://prove2.me/theorems/9b5392f3-0590-4637-9228-ac12482fdfb5
-- title:
--   Unitary Norm Counts: card conj
-- statement:
--   The Unitary Norm Counts construction uses the card conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardMapEquiv.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardMapEquiv.lean#L11-L43

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

theorem Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_conj (C : Matrix m m A) (hC : IsUnit C.det) :
    Nat.card {X : Matrix m m A // Xᴴ * (Cᴴ * C) * X = Cᴴ * C} =
      Nat.card {Y : Matrix m m A // Yᴴ * Y = 1} := by sorry
