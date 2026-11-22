-- Prove2me | Theorems.Thm_Auto_exists_trig_approx
-- name    : Auto.exists_trig_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:54.12544+00:00
-- url     : https://prove2.me/theorems/cac2bc6d-999b-4fe7-bc0a-e6b97e2a1855
-- title:
--   Auto: exists trig approx
-- statement:
--   Continuous 1-periodic functions are uniform limits of trigonometric polynomials.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L971-L985
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L971-L985

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

theorem Auto.exists_trig_approx {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ P : ℝ → ℂ, Continuous P ∧ Function.Periodic P 1 ∧
      (∃ K : ℕ, ∀ N ≥ K, ∀ x, fourierPartialSum P N x = P x) ∧ ∀ x, ‖f x - P x‖ < δ := by sorry
