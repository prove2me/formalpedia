-- Prove2me | Theorems.Thm_Auto_integrable_of_norm_le_of_vanish
-- name    : Auto.integrable_of_norm_le_of_vanish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:44.136841+00:00
-- url     : https://prove2.me/theorems/8dcb40fb-8cdd-4533-9881-15dfb5c05e80
-- title:
--   Auto: integrable of norm le of vanish
-- statement:
--   A bounded measurable function on the line vanishing outside a compact interval is integrable.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L36-L45
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L36-L45

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section

theorem Auto.integrable_of_norm_le_of_vanish {E : Type*} [NormedAddCommGroup E] {h : ℝ → E} {A B : ℝ}
    (hm : AEStronglyMeasurable h volume) (hB : ∀ x, ‖h x‖ ≤ B)
    (hs : ∀ x, A < |x| → h x = 0) : Integrable h := by sorry
