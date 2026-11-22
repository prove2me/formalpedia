-- Prove2me | Theorems.Thm_Auto_ae_tendsto_carlesonMoll
-- name    : Auto.ae_tendsto_carlesonMoll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:12.668393+00:00
-- url     : https://prove2.me/theorems/c86a6601-94d2-4900-8fc1-66960f5cfd61
-- title:
--   Auto: ae tendsto carleson Moll
-- statement:
--   The Auto construction uses the ae tendsto carleson Moll property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L600-L608
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L600-L608

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Auto.ae_tendsto_carlesonMoll [CompleteSpace E] {h : ℝ → E} (hh : LocallyIntegrable h) :
    ∀ᵐ x, Tendsto (fun k => carlesonMoll k h x) atTop (𝓝 (h x)) := by sorry
