-- Prove2me | Theorems.Thm_Auto_ae_fst_of_ae
-- name    : Auto.ae_fst_of_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:23.374953+00:00
-- url     : https://prove2.me/theorems/ec096d7c-5765-4c5d-9363-9050e239597a
-- title:
--   Auto: ae fst of ae
-- statement:
--   The Auto construction uses the ae fst of ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L614-L616
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L614-L616

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

theorem Auto.ae_fst_of_ae {P : ℝ → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ p : ℝ × ℝ, P p.1 := by sorry
