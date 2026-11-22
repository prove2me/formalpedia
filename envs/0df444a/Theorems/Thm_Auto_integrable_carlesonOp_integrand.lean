-- Prove2me | Theorems.Thm_Auto_integrable_carlesonOp_integrand
-- name    : Auto.integrable_carlesonOp_integrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:03:09.255807+00:00
-- url     : https://prove2.me/theorems/4ec8c0d1-7e3f-40c4-bfb9-dc0624f5ef6e
-- title:
--   Auto: integrable carleson Op integrand
-- statement:
--   The Auto construction uses the integrable carleson Op integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1037-L1045
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1037-L1045

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
open Real

theorem Auto.integrable_carlesonOp_integrand {h : ℝ → ℂ} {B : ℝ} (hh : Measurable h)
    (hB : ∀ x, ‖h x‖ ≤ B) (v x : ℝ) :
    Integrable fun t => h (x - t) * ((carlesonWeight t * Real.sin (v * t) / t : ℝ) : ℂ) := by sorry
