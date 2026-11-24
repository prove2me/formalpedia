-- Prove2me | solution 1 for scalar_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:44:46.715805+00:00
-- url     : https://prove2.me/submissions/4c9d41be-4374-49ef-8b3c-36434b4eb78f

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter Topology
open scoped RealInnerProductSpace
open ShorNonsmooth.Stochastic
open ShorNonsmooth.SubgradMethod

theorem solution (d w s : ℕ → ℝ)
    (hd : ∀ k, 0 ≤ d k) (hw : ∀ k, 0 < w k)
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, w k) atTop atTop)
    (hs : Tendsto s atTop (𝓝 0))
    (hjump : ∀ᶠ k in atTop, d (k+1) ≤ d k + s k)
    (hdesc : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in atTop, ε ≤ d k → d (k+1)^2 ≤ d k^2-c*w k) :
    Tendsto d atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  obtain ⟨c, hc, hev⟩ := hdesc (ε / 2) he
  have hs' : ∀ᶠ k in atTop, s k < ε / 2 := hs (Iio_mem_nhds he)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hjump.and (hev.and hs'))
  -- (a) some index beyond `K` has `d < ε/2`
  have ha : ∃ k₀, K ≤ k₀ ∧ d k₀ < ε / 2 := by
    by_contra hcon
    push Not at hcon
    have tele : ∀ m, d (K + m) ^ 2 ≤ d K ^ 2 - c * ∑ k ∈ Finset.range m, w (K + k) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ← add_assoc]
        have := (hK (K + m) (by omega)).2.1 (hcon _ (by omega))
        nlinarith
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hdiv.eventually_ge_atTop (∑ k ∈ Finset.range K, w k + d K ^ 2 / c + 1))
    have h1 := hN (K + N) (by omega)
    rw [Finset.sum_range_add] at h1
    have h2 := tele N
    have h3 : c * (d K ^ 2 / c + 1) ≤ c * ∑ k ∈ Finset.range N, w (K + k) :=
      mul_le_mul_of_nonneg_left (by linarith) hc.le
    rw [mul_add, mul_div_cancel₀ _ hc.ne'] at h3
    nlinarith [sq_nonneg (d (K + N))]
  obtain ⟨k₀, hk₀K, hk₀⟩ := ha
  -- (b) once below `ε/2`, the sequence stays below `ε`
  have hb : ∀ j, d (k₀ + j) < ε := by
    intro j
    induction j with
    | zero => simp; linarith
    | succ j ih =>
      rw [← add_assoc]
      obtain ⟨hj1, hj2, hj3⟩ := hK (k₀ + j) (by omega)
      by_cases hcase : ε / 2 ≤ d (k₀ + j)
      · have := hj2 hcase
        have hwpos := hw (k₀ + j)
        have hsq : d (k₀ + j + 1) ^ 2 ≤ d (k₀ + j) ^ 2 := by nlinarith
        have := (pow_le_pow_iff_left₀ (hd _) (hd _) (by norm_num : (2:ℕ) ≠ 0)).1 hsq
        linarith
      · push Not at hcase
        linarith
  refine ⟨k₀, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_0_eq_abs, abs_of_nonneg (hd _)]
  exact hb j
