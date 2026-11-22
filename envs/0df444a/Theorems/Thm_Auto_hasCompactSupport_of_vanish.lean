-- Prove2me | Theorems.Thm_Auto_hasCompactSupport_of_vanish
-- name    : Auto.hasCompactSupport_of_vanish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:35.362108+00:00
-- url     : https://prove2.me/theorems/02073140-3725-4d29-91a5-598a15391ee5
-- title:
--   Auto: has Compact Support of vanish
-- statement:
--   The Auto construction uses the has Compact Support of vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L47-L50
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L47-L50

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

theorem Auto.hasCompactSupport_of_vanish {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {A : ℝ}
    (hf : ∀ x, A < |x| → f x = 0) : HasCompactSupport f := by sorry
