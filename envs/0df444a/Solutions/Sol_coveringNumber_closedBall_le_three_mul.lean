-- Prove2me | solution 1 for coveringNumber_closedBall_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:48:42.476362+00:00
-- url     : https://prove2.me/submissions/ab3c083f-b94f-4e62-b1a7-e3c58ca64821

import Definitions.Def_BrownianMotion_Continuity_CoveringNumber_F001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Covering and packing numbers

### References
- Vershynin, High-Dimensional Probability (section 4.2)
-/

@[expose] public section

open EMetric Set Metric
open scoped ENNReal NNReal

section PseudoEMetricSpace

variable {E : Type*} [PseudoEMetricSpace E] {r ε ε' : ℝ≥0} {A B C : Set E}

end PseudoEMetricSpace

section Volume

open MeasureTheory

section PseudoEMetricSpace
variable {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0} {s N : Set X}

end PseudoEMetricSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ε : ℝ≥0} {A : Set E} {C : Set E}

open scoped Pointwise in
open MeasureTheory in
theorem _root_.solution [Nontrivial E]
    {x : E} {r : ℝ≥0} (hr_zero : r ≠ 0) (hε : ε ≤ r) :
    (coveringNumber ε (Metric.closedEBall x r) : ℝ≥0∞)
      ≤ (3 * r / (ε : ℝ≥0∞)) ^ (Module.finrank ℝ E) := by
  set d := Module.finrank ℝ E with hd
  have hdpos : 0 < d := Module.finrank_pos
  rcases eq_or_ne ε 0 with h0 | h0
  · subst h0
    have : (3 * (r : ℝ≥0∞) / ((0 : ℝ≥0) : ℝ≥0∞)) = ⊤ := by
      rw [ENNReal.coe_zero, ENNReal.div_zero]
      exact mul_ne_zero (by norm_num) (by exact_mod_cast hr_zero)
    rw [this, ENNReal.top_pow hdpos.ne']
    exact le_top
  have hεpos : 0 < ε := pos_iff_ne_zero.2 h0
  have h1 := coveringNumber_le_volume_div (Metric.closedEBall x r) hεpos
  rw [show (ε : ℝ≥0∞) / 2 = ((ε / 2 : ℝ≥0) : ℝ≥0∞) by simp] at h1
  rw [Metric.closedEBall_coe, Metric.closedEBall_coe] at h1
  have hsub : Metric.closedBall x (r : ℝ) + Metric.closedBall (0 : E) ((ε / 2 : ℝ≥0) : ℝ)
      ⊆ Metric.closedBall x ((r : ℝ) + ((ε / 2 : ℝ≥0) : ℝ)) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Metric.mem_closedBall] at ha hb ⊢
    rw [dist_eq_norm] at ha ⊢
    rw [dist_zero_right] at hb
    calc ‖a + b - x‖ = ‖(a - x) + b‖ := by congr 1; abel
      _ ≤ ‖a - x‖ + ‖b‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ha hb
  have hvol := measure_mono (μ := volume) hsub
  set e2 : ℝ := ((ε / 2 : ℝ≥0) : ℝ) with he2
  have he2pos : 0 < e2 := by rw [he2]; exact_mod_cast (half_pos hεpos)
  have hrpos : (0 : ℝ) ≤ r := r.coe_nonneg
  rw [Measure.addHaar_closedBall volume x (by positivity)] at hvol
  rw [Measure.addHaar_closedBall volume 0 he2pos.le] at h1
  set c := volume (Metric.ball (0 : E) 1) with hc
  have hc0 : c ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  rw [Metric.closedEBall_coe]
  refine h1.trans ?_
  refine (ENNReal.div_le_div_right hvol _).trans ?_
  rw [ENNReal.mul_div_mul_right _ _ hc0 hctop, ← ENNReal.ofReal_div_of_pos (by positivity),
    ← div_pow]
  have hε' : (ε : ℝ) ≤ r := by exact_mod_cast hε
  have he2v : e2 = (ε : ℝ) / 2 := by rw [he2]; push_cast; ring
  have hq : ((r : ℝ) + e2) / e2 ≤ 3 * r / ε := by
    rw [div_le_div_iff₀ he2pos (by exact_mod_cast hεpos), he2v]
    nlinarith
  have hrhs : (3 * (r : ℝ≥0∞) / (ε : ℝ≥0∞)) ^ d = ENNReal.ofReal ((3 * r / ε) ^ d) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos (by exact_mod_cast hεpos),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    norm_num
  rw [hrhs]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hq d)

end Volume
