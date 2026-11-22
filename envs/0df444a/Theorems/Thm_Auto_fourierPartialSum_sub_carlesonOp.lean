-- Prove2me | Theorems.Thm_Auto_fourierPartialSum_sub_carlesonOp
-- name    : Auto.fourierPartialSum_sub_carlesonOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:03:07.22151+00:00
-- url     : https://prove2.me/theorems/eb1158d0-8ccb-48c0-9cba-676fbc428d58
-- title:
--   Auto: fourier Partial Sum sub carleson Op
-- statement:
--   The Fourier partial sums differ from the modulated kernel by a uniformly bounded error.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1048-L1153
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1048-L1153

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

theorem Auto.fourierPartialSum_sub_carlesonOp {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) {δ : ℝ} (hδ : ∀ x, ‖g x‖ ≤ δ) {R x : ℝ} (hx : |x| ≤ R) (N : ℕ) :
    ‖fourierPartialSum g N x - ((1 / (π * carlesonMass) : ℝ) : ℂ) *
      carlesonOp ((Icc (-(R + 11)) (R + 11)).indicator g) (fun _ => (2 * N + 1) * π) x‖ ≤
        22 * δ := by sorry
