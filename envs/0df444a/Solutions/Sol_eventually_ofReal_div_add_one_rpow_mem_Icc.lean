-- Prove2me | solution 1 for eventually_ofReal_div_add_one_rpow_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/d410d851-e852-4124-a519-ee4673b7f3c3

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
theorem _root_.solution {d : ℝ} {ε : ℝ≥0∞} (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ k : ℝ, k ≥ 0 ∧ ∀ k' ≥ k, ENNReal.ofReal ((k' / (k' + 1)) ^ d) ∈ Set.Icc (1 - ε) (1 + ε) := by
  have hshift : Tendsto (fun k : ℝ => k + 1) atTop atTop := by
    simpa using (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  have hzero : Tendsto (fun k : ℝ => 1 / (k + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hshift
  have hratio : Tendsto (fun k : ℝ => k / (k + 1)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hnear : Tendsto (fun k : ℝ => 1 - 1 / (k + 1)) atTop (𝓝 1) := by
      simpa only [sub_zero] using hone.sub hzero
    refine hnear.congr' ?_
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with k hk
    have hne : k + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hrpow : Tendsto (fun k : ℝ => (k / (k + 1)) ^ d) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.one_rpow] using
      (Real.continuous_rpow_const hd).continuousAt.tendsto.comp hratio
  have hlimit : Tendsto (fun k : ℝ => ENNReal.ofReal ((k / (k + 1)) ^ d))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrpow
  have hlower : 1 - ε < (1 : ℝ≥0∞) :=
    ENNReal.sub_lt_self (by simp) (by simp) (ne_of_gt hε)
  have hupper : (1 : ℝ≥0∞) < 1 + ε := by
    exact ENNReal.lt_add_right (by simp) (ne_of_gt hε)
  obtain ⟨k, hk⟩ := eventually_atTop.1 (hlimit.eventually (Ioo_mem_nhds hlower hupper))
  refine ⟨max k 0, le_max_right _ _, ?_⟩
  intro k' hk'
  have hmem := hk k' (le_trans (le_max_left _ _) hk')
  exact ⟨hmem.1.le, hmem.2.le⟩
