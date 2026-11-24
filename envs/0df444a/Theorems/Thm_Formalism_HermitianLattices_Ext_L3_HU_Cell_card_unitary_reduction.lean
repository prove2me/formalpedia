-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_card_unitary_reduction
-- name    : Formalism.HermitianLattices.Ext.L3.HU.Cell.card_unitary_reduction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:29.354707+00:00
-- url     : https://prove2.me/theorems/ddd47241-b5b0-47df-b8a8-df86820ff08a
-- title:
--   Cell: card unitary reduction
-- statement:
--   The Cell construction uses the card unitary reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L45-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L45-L103

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
open Formalism.HermitianLattices.Ext.L3.HU.Cell
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A A' C : Type*} [CommRing A] [StarRing A] [CommRing A'] [CommRing C] [StarRing C]

theorem Formalism.HermitianLattices.Ext.L3.HU.Cell.card_unitary_reduction [Finite A] (π : A →+* A') (ρ : A →+* C) (μ : C →+ A)
    (hμi : Function.Injective μ) (hμr : ∀ a, π a = 0 ↔ ∃ y, μ y = a)
    (hμs : ∀ y, μ (star y) = star (μ y)) (hμm : ∀ a y, μ (ρ a * y) = a * μ y)
    (h2 : ∀ y z, μ y * μ z = 0) (H : Matrix κ κ A)
    (hu : ∀ X : Matrix κ κ A, Xᴴ * H * X = H → IsUnit X.det) :
    Nat.card {X : Matrix κ κ A // Xᴴ * H * X = H} =
      Nat.card {X' : Matrix κ κ A' // ∃ X : Matrix κ κ A, Xᴴ * H * X = H ∧ X.map π = X'} *
        Nat.card {Y : Matrix κ κ C // H.map ρ * Y + Yᴴ * H.map ρ = 0} := by sorry
