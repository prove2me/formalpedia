-- Prove2me | solution 2 for eventually_ofReal_div_add_one_rpow_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:38.152183+00:00
-- url     : https://prove2.me/submissions/19fccb87-9d7a-490c-8408-b54cca829ab9

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


theorem solution {d : ℝ} {ε : ℝ≥0∞} (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  by_cases htop : ε = ⊤
  · subst htop
    exact ⟨0, le_rfl, fun k' _ => ⟨by simp, by simp⟩⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  have hq : Filter.Tendsto (fun k' : ℝ => k' / (k' + 1)) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun k' : ℝ => 1 - (k' + 1)⁻¹) Filter.atTop (nhds 1) := by
      have := (tendsto_const_nhds (x := (1:ℝ))).sub
        (tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id))
      simpa using this
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with k' hk'
    field_simp
    ring
  have hlim : Filter.Tendsto (fun k' : ℝ => (k' / (k' + 1)) ^ d) Filter.atTop (nhds 1) := by
    have := (Real.continuousAt_rpow_const 1 d (Or.inl one_ne_zero)).tendsto.comp hq
    rw [Real.one_rpow] at this
    exact this
  have hev := (hlim.eventually (lt_mem_nhds (show 1 - ε.toReal < 1 by linarith))).and
    (Filter.eventually_ge_atTop (0:ℝ))
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max k 0, le_max_right _ _, fun k' hk' => ?_⟩
  obtain ⟨h1, h2⟩ := hk k' (le_trans (le_max_left _ _) hk')
  have hx0 : 0 ≤ (k' / (k' + 1)) ^ d := Real.rpow_nonneg (by positivity) _
  have hx1 : (k' / (k' + 1)) ^ d ≤ 1 :=
    Real.rpow_le_one (by positivity) (div_le_one_of_le₀ (by linarith) (by positivity)) hd
  constructor
  · rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((k' / (k' + 1)) ^ d + ε.toReal) :=
          ENNReal.one_le_ofReal.2 (by linarith)
      _ = ENNReal.ofReal ((k' / (k' + 1)) ^ d) + ENNReal.ofReal ε.toReal :=
          ENNReal.ofReal_add hx0 ENNReal.toReal_nonneg
      _ = ENNReal.ofReal ((k' / (k' + 1)) ^ d) + ε := by rw [ENNReal.ofReal_toReal htop]
  · exact le_trans (ENNReal.ofReal_le_one.2 hx1) le_self_add

