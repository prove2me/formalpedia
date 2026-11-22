-- Prove2me | Theorems.Thm_Auto_classical_carleson
-- name    : Auto.classical_carleson
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:39:22.591129+00:00
-- url     : https://prove2.me/theorems/f32ddce9-50a6-419f-bc31-2f36592495c6
-- title:
--   Auto: classical carleson
-- statement:
--   The Auto construction uses the classical carleson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1475-L1477
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1475-L1477

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

theorem Auto.classical_carleson (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N ↦ Triangular.fourierPartialSum f N x) atTop (𝓝 (f x)) := by sorry
