-- Prove2me | solution 2 for volume_ball_div_volume_ball_add_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:42.935284+00:00
-- url     : https://prove2.me/submissions/3eb3a678-0ca2-4a83-a584-a52b184b483f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)
open ZSpan
variable (b : Basis ι ℤ S.lattice)
open MeasureTheory Measure Metric ZSpan
variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)
open Filter Topology
open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace


theorem solution {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hq' : Tendsto (fun R : ℝ => R / (R + C)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun R : ℝ => 1 - C * (R + C)⁻¹) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1:ℝ))).sub
        ((tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ C tendsto_id)).const_mul C)
      simpa using this
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    have : R + C ≠ 0 := by linarith
    field_simp
    ring
  have hp : Tendsto (fun R : ℝ => ENNReal.ofReal ((R / (R + C)) ^ d)) atTop (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (hq'.pow d)
    rwa [one_pow, ENNReal.ofReal_one] at this
  refine hp.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  have hK : 0 < Real.sqrt Real.pi ^ Fintype.card (Fin d) /
      Real.Gamma ((Fintype.card (Fin d) : ℝ) / 2 + 1) :=
    div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball,
    ENNReal.mul_div_mul_right _ _ (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top,
    Fintype.card_fin, div_pow, ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow hR.le, ENNReal.ofReal_pow (by linarith)]

