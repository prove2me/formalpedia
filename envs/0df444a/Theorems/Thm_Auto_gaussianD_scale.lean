-- Prove2me | Theorems.Thm_Auto_gaussianD_scale
-- name    : Auto.gaussianD_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:24.282092+00:00
-- url     : https://prove2.me/theorems/3659d5fb-af6a-4050-a2cf-a1306922485b
-- title:
--   Auto: gaussian D scale
-- statement:
--   The Auto construction uses the gaussian D scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L208-L213
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L208-L213

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
open Real

theorem Auto.gaussianD_scale (j : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (t : ℝ) :
    gaussianD j (a * s) t = (√s)⁻¹ ^ (j + 1) * gaussianD j a ((√s)⁻¹ * t) := by sorry
