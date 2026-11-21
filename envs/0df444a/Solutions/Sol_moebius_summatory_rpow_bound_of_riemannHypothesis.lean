-- Prove2me | solution 1 for moebius_summatory_rpow_bound_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-20T23:13:26.788694+00:00
-- url     : https://prove2.me/submissions/3b9e9d65-002e-4a44-bce6-60d1dffde293

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.RemovableSingularity
import Theorems.Thm_Titchmarsh_inv_riemannZeta_le_rpow_of_riemannHypothesis
import Theorems.Thm_Titchmarsh_partialSum_isBigO_of_holomorphic_growth

open Filter Topology

/-- Under RH, `ζ` has no zeros with `Re s > 1/2`. -/
lemma zeta_ne_zero_of_half_lt_re (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta s ≠ 0 := by
  intro h0
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 h0
  · have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [this] at hs
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have := hRH s h0 htriv hs1
    linarith

theorem solution (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
  -- the holomorphic continuation of `∑ μ(n) n^{-s}` to `Re s > 1/2`
  set F : ℂ → ℂ := Function.update (fun s => (riemannZeta s)⁻¹) 1 0 with hFdef
  have hF_ne : ∀ s : ℂ, s ≠ 1 → F s = (riemannZeta s)⁻¹ := fun s hs => by
    simp [hFdef, Function.update_of_ne hs]
  have hU : {s : ℂ | (1 : ℝ) / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hFdiff : DifferentiableOn ℂ F {s : ℂ | (1 : ℝ) / 2 < s.re} := by
    rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff hU]
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs1 : s ≠ 1 := hs.2
      have hre : (1 : ℝ) / 2 < s.re := hs.1
      have hd : DifferentiableAt ℂ (fun s => (riemannZeta s)⁻¹) s :=
        (differentiableAt_riemannZeta hs1).inv (zeta_ne_zero_of_half_lt_re hRH hre)
      have heq : F =ᶠ[𝓝 s] fun s => (riemannZeta s)⁻¹ := by
        filter_upwards [isOpen_ne.mem_nhds hs1] with z hz using hF_ne z hz
      exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
      have hF1 : F 1 = 0 := by simp [hFdef]
      rw [hF1]
      have hlim : Tendsto (fun s : ℂ => (s - 1) * ((s - 1) * riemannZeta s)⁻¹) (𝓝[≠] 1)
          (𝓝 ((1 - 1) * (1 : ℂ)⁻¹)) := by
        refine Tendsto.mul ?_ (riemannZeta_residue_one.inv₀ one_ne_zero)
        exact ((continuous_id.sub continuous_const).tendsto' 1 (1 - 1) rfl).mono_left
          nhdsWithin_le_nhds
      simp only [sub_self, zero_mul] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
      rw [hF_ne s hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs', one_mul]
  have hFL : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s := by
    intro s hs
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    rw [hF_ne s hs1, ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    have := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    exact (eq_inv_of_mul_eq_one_right this).symm
  have hgrowth : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      1 / 2 + δ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖F s‖ ≤ C * |s.im| ^ ε := by
    intro δ hδ ε hε
    obtain ⟨C, hC⟩ :=
      Titchmarsh.inv_riemannZeta_le_rpow_of_riemannHypothesis hRH δ hδ ε hε
    refine ⟨C, fun s h1 h2 h3 => ?_⟩
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at h3
    rw [hF_ne s hs1]
    exact hC s h1 h2 h3
  have ha : ∀ n : ℕ, ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact Titchmarsh.partialSum_isBigO_of_holomorphic_growth
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) ha (1 / 2) (by norm_num) F hFdiff hFL
    hgrowth
