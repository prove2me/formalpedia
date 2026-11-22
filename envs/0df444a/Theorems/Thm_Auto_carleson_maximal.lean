-- Prove2me | Theorems.Thm_Auto_carleson_maximal
-- name    : Auto.carleson_maximal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T19:03:32.068519+00:00
-- url     : https://prove2.me/theorems/1acb3d33-67a2-44e5-aa4b-353b2b8bda51
-- title:
--   Auto: carleson maximal
-- statement:
--   Linearized maximal estimate for the modulated kernels at the Dirichlet frequencies.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1290-L1367
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1290-L1367

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

theorem Auto.carleson_maximal (R : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ → ℂ) (B lam : ℝ), Measurable h →
    (∀ x, ‖h x‖ ≤ B) → (∀ x, R + 11 < |x| → h x = 0) → 0 < lam →
    volume {x | x ∈ Icc (-R) R ∧ ∃ N : ℕ, lam < ‖carlesonOp h (fun _ => (2 * N + 1) * π) x‖} ≤
      ENNReal.ofReal (4 * (2 * K * B / lam) ^ 3) := by sorry
