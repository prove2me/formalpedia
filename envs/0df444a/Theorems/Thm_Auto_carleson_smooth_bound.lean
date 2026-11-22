-- Prove2me | Theorems.Thm_Auto_carleson_smooth_bound
-- name    : Auto.carleson_smooth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:46.871469+00:00
-- url     : https://prove2.me/theorems/b38b7bb2-ea09-4816-8c1d-7faf90367c4a
-- title:
--   Auto: carleson smooth bound
-- statement:
--   The triangular theorem bounds the smooth modulated sine form.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L397-L472
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L397-L472

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

theorem Auto.carleson_smooth_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a ν : ℝ → ℝ) (g : ℝ → ℂ) (A L : ℝ),
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ ν → ContDiff ℝ ∞ g →
    (∀ x, A < |x| → a x = 0) → (∀ x, L < |x| → g x = 0) →
    ‖carlesonForm a ν g‖ ≤ C * (eLpNorm (carlesonF₀ a ν 1) 3 volume).toReal *
      (eLpNorm (carlesonF₁ g) 3 volume).toReal * (eLpNorm (carlesonF₂ a ν 1) 3 volume).toReal := by sorry
