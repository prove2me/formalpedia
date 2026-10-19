-- Prove2me | solution 1 for volume_ball_div_volume_ball_add_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/ebc1b1f8-a783-4cc8-9dea-7488d6c73de4

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
theorem _root_.solution {C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))) atTop (𝓝 1) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let c : ℝ≥0∞ := ENNReal.ofReal
    (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1))
  have hc : c ≠ 0 := by
    have hb : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
      ne_of_gt (measure_ball_pos (μ := volume) 0 (by norm_num))
    rw [EuclideanSpace.volume_ball] at hb
    simpa [c] using hb
  have hctop : c ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have hshift : Tendsto (fun R : ℝ => R + C) atTop atTop := by
    simpa using (tendsto_atTop_add_const_right atTop C tendsto_id)
  have hzero : Tendsto (fun R : ℝ => C / (R + C)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hshift
  have hratio : Tendsto (fun R : ℝ => R / (R + C)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hnear : Tendsto (fun R : ℝ => 1 - C / (R + C)) atTop (𝓝 1) := by
      simpa only [sub_zero] using hone.sub hzero
    refine hnear.congr' ?_
    filter_upwards [eventually_gt_atTop (-C)] with R hR
    have hne : R + C ≠ 0 := by linarith
    field_simp
    ring
  have hpow : Tendsto (fun R : ℝ => (R / (R + C)) ^ d) atTop (𝓝 1) := by
    simpa using hratio.pow d
  have hlimit : Tendsto (fun R : ℝ => ENNReal.ofReal ((R / (R + C)) ^ d))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpow
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hRC : 0 < R + C := by linarith
  symm
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  change ENNReal.ofReal R ^ d * c / (ENNReal.ofReal (R + C) ^ d * c) = _
  rw [ENNReal.mul_div_mul_right _ _ hc hctop,
    ← ENNReal.ofReal_pow hR.le d, ← ENNReal.ofReal_pow hRC.le d,
    ← ENNReal.ofReal_div_of_pos (pow_pos hRC d), ← div_pow]
