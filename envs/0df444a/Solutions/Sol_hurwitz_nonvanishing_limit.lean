-- Prove2me | solution 1 for hurwitz_nonvanishing_limit
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T01:19:45.530123+00:00
-- url     : https://prove2.me/submissions/0d14f735-284d-4839-9c95-fb1904768166

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic.Linarith

open Complex Finset Filter Topology

theorem solution
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf_holo : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hf_nz : ∀ n, ∀ z ∈ U, f n z ≠ 0)
    (hconv : TendstoUniformlyOn f g atTop U)
    (hg_not_zero : ∃ z ∈ U, g z ≠ 0) :
    ∀ z ∈ U, g z ≠ 0 := by
  have hg_diff : DifferentiableOn ℂ g U :=
    hconv.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun n => (hf_holo n).differentiableOn) hU
  have hg_holo : AnalyticOnNhd ℂ g U := hg_diff.analyticOnNhd hU
  intro z hzU hgz

  have hpunct : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
    rcases (hg_holo z hzU).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · have hg_zero : Set.EqOn g 0 U :=
        hg_holo.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hzU hzero
      obtain ⟨w, hwU, hgw⟩ := hg_not_zero
      exact (hgw (hg_zero hwU)).elim
    · exact hne

  obtain ⟨r₁, hr₁, hr₁_nz⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  obtain ⟨r₂, hr₂, hr₂U⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  let r := min r₁ r₂ / 2
  have hr : 0 < r := div_pos (lt_min hr₁ hr₂) zero_lt_two
  have hclosed_U : Metric.closedBall z r ⊆ U := by
    intro w hw
    apply hr₂U
    rw [Metric.mem_ball]
    have hw' := Metric.mem_closedBall.mp hw
    dsimp [r] at hw' ⊢
    nlinarith [min_le_right r₁ r₂]
  have hclosed_nz : ∀ w ∈ Metric.closedBall z r, w ≠ z → g w ≠ 0 := by
    intro w hw hwz
    apply hr₁_nz
    constructor
    · rw [Metric.mem_ball]
      have hw' := Metric.mem_closedBall.mp hw
      dsimp [r] at hw' ⊢
      nlinarith [min_le_left r₁ r₂]
    · simpa using hwz

  have hsphere_ne : (Metric.sphere z r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  have hg_cont : ContinuousOn (fun w => ‖g w‖) (Metric.sphere z r) :=
    ((hg_holo.continuousOn.mono (Metric.sphere_subset_closedBall.trans hclosed_U)).norm)
  obtain ⟨w₀, hw₀, hw₀_min⟩ :=
    (isCompact_sphere z r).exists_isMinOn hsphere_ne hg_cont
  let δ := ‖g w₀‖
  have hδ : 0 < δ := by
    apply norm_pos_iff.mpr
    apply hclosed_nz w₀ (Metric.sphere_subset_closedBall hw₀)
    exact Metric.ne_of_mem_sphere hw₀ hr.ne'
  have hg_sphere : ∀ w ∈ Metric.sphere z r, δ ≤ ‖g w‖ := by
    intro w hw
    exact hw₀_min hw

  have hclose :
      ∀ᶠ n in atTop, ∀ w ∈ U, dist (g w) (f n w) < δ / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hconv) (δ / 2) (half_pos hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hclose
  have hf_sphere :
      ∀ n ≥ N, ∀ w ∈ Metric.sphere z r, δ / 2 ≤ ‖f n w‖ := by
    intro n hn w hw
    have hfg := hN n hn w (hclosed_U (Metric.sphere_subset_closedBall hw))
    rw [dist_eq_norm] at hfg
    have hrev := norm_sub_norm_le (g w) (f n w)
    have hg_lower := hg_sphere w hw
    linarith

  have hinv_bound : ∀ n ≥ N, ‖(f n z)⁻¹‖ ≤ (δ / 2)⁻¹ := by
    intro n hn
    have hinv_diff :
        DifferentiableOn ℂ (fun w => (f n w)⁻¹) (Metric.closedBall z r) :=
      ((hf_holo n).differentiableOn.mono hclosed_U).inv
        (fun w hw => hf_nz n w (hclosed_U hw))
    have hinv_cl :
        DiffContOnCl ℂ (fun w => (f n w)⁻¹) (Metric.closedBall z r) := by
      apply DifferentiableOn.diffContOnCl
      simpa only [Metric.closure_closedBall] using hinv_diff
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
        Metric.isBounded_closedBall hinv_cl
    · intro w hw
      have hws : w ∈ Metric.sphere z r :=
        Metric.frontier_closedBall_subset_sphere hw
      rw [norm_inv]
      exact inv_anti₀ (half_pos hδ) (hf_sphere n hn w hws)
    · exact subset_closure (Metric.mem_closedBall_self hr.le)

  have hnorm_zero : Tendsto (fun n => ‖f n z‖) atTop (𝓝 0) := by
    simpa only [hgz, norm_zero] using (hconv.tendsto_at hzU).norm
  have hnorm_pos : Tendsto (fun n => ‖f n z‖) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hnorm_zero, Eventually.of_forall fun n => norm_pos_iff.mpr (hf_nz n z hzU)⟩
  have hinv_top : Tendsto (fun n => ‖(f n z)⁻¹‖) atTop atTop := by
    rw [show (fun n => ‖(f n z)⁻¹‖) = (fun n => ‖f n z‖)⁻¹ by
      ext n
      simp]
    exact hnorm_pos.inv_tendsto_nhdsGT_zero
  obtain ⟨n, hnlarge, hn⟩ :=
    (hinv_top.eventually_gt_atTop ((δ / 2)⁻¹)).and (eventually_ge_atTop N) |>.exists
  exact (not_lt_of_ge (hinv_bound n hn)) hnlarge
