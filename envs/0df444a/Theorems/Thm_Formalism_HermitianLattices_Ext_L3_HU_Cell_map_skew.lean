-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_map_skew
-- name    : Formalism.HermitianLattices.Ext.L3.HU.Cell.map_skew
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:49.857477+00:00
-- url     : https://prove2.me/theorems/509ab6f7-3221-4b2d-8af5-e97303e09135
-- title:
--   Cell: map skew
-- statement:
--   The Cell construction uses the map skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean#L18-L26

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

theorem Formalism.HermitianLattices.Ext.L3.HU.Cell.map_skew (ρ : A →+* C) (μ : C →+ A) (hμs : ∀ y, μ (star y) = star (μ y))
    (hμm : ∀ a y, μ (ρ a * y) = a * μ y) (H : Matrix κ κ A) (Y : Matrix κ κ C) :
    (H.map ρ * Y + Yᴴ * H.map ρ).map μ = H * Y.map μ + (Y.map μ)ᴴ * H := by sorry
