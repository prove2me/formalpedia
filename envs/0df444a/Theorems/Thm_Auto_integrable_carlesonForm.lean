-- Prove2me | Theorems.Thm_Auto_integrable_carlesonForm
-- name    : Auto.integrable_carlesonForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:41.247744+00:00
-- url     : https://prove2.me/theorems/be9377d1-7475-45b4-bf07-249fca96ca91
-- title:
--   Auto: integrable carleson Form
-- statement:
--   The Auto construction uses the integrable carleson Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L365-L382
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L365-L382

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

theorem Auto.integrable_carlesonForm {a ν : ℝ → ℝ} {g : ℝ → ℂ} {B : ℝ}
    (ha : Measurable a) (hν : Measurable ν) (hg : Measurable g) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hi : Integrable fun x => a x ^ 2 * |ν x|) :
    Integrable fun p : ℝ × ℝ => (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) *
      ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ) := by sorry
