-- Prove2me | Theorems.Thm_Auto_carleson_rough_bound
-- name    : Auto.carleson_rough_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T19:02:16.986631+00:00
-- url     : https://prove2.me/theorems/6fab7a67-714c-4d9f-b5dc-f1a757912384
-- title:
--   Auto: carleson rough bound
-- statement:
--   The triangular theorem bounds the modulated sine form for an indicator and rough data.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L623-L781
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L623-L781

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

theorem Auto.carleson_rough_bound (L : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set ℝ) (ν : ℝ → ℝ) (g : ℝ → ℂ)
    (R V B : ℝ), MeasurableSet F → F ⊆ Icc (-R) R → Measurable ν → (∀ x, |ν x| ≤ V) →
    Measurable g → (∀ x, ‖g x‖ ≤ B) → (∀ x, L < |x| → g x = 0) →
    ‖carlesonForm (F.indicator 1) ν g‖ ≤ K * B * (volume F).toReal ^ (2 / 3 : ℝ) := by sorry
