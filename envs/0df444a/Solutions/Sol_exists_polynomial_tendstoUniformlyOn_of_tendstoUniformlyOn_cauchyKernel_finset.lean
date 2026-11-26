-- Prove2me | solution 1 for exists_polynomial_tendstoUniformlyOn_of_tendstoUniformlyOn_cauchyKernel_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:23.183611+00:00
-- url     : https://prove2.me/submissions/abeeb071-0aab-42ad-9c2e-7e59915c7a37

import Definitions.Def_Operator_Crouzeix_ConvexRungeFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_Operator_Crouzeix_ConvexRungeClosure
import Theorems.Thm_exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex

section
open Filter Polynomial Set
open scoped Topology
private theorem exists_polynomial_tendstoUniformlyOn_of_iterated_limits
    (K : Set ℂ) (f : ℂ → ℂ) (g : ℕ → ℂ → ℂ)
    (hg : TendstoUniformlyOn g f atTop K)
    (hpoly : ∀ n, ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun j z => Polynomial.eval z (q j))
        (g n) atTop K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => Polynomial.eval z (q n))
        f atTop K := by
  choose q hq using hpoly
  have hevent : ∀ n : ℕ, ∀ᶠ j in atTop,
      ∀ z ∈ K, dist (g n z) (Polynomial.eval z (q n j)) <
        1 / ((n : ℝ) + 1) := by
    intro n
    apply (Metric.tendstoUniformlyOn_iff.mp (hq n))
    positivity
  choose N hN using fun n => eventually_atTop.1 (hevent n)
  refine ⟨fun n => q n (N n), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hg_event : ∀ᶠ n in atTop,
      ∀ z ∈ K, dist (f z) (g n z) < ε / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hg) (ε / 2) (by positivity)
  have hrate : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrate_event : ∀ᶠ (n : ℕ) in atTop,
      1 / ((n : ℝ) + 1) < ε / 2 :=
    hrate.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hg_event, hrate_event] with n hgn hn z hz
  calc
    dist (f z) (Polynomial.eval z (q n (N n))) ≤
        dist (f z) (g n z) +
          dist (g n z) (Polynomial.eval z (q n (N n))) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add (hgn z hz) ((hN n (N n) le_rfl z hz).trans hn)
    _ = ε := by ring
end

set_option autoImplicit false
open Filter Polynomial Set
open scoped Topology
theorem _root_.solution
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (poles : ℕ → Finset ℂ) (coeff : ℕ → ℂ → ℂ)
    (hpoles : ∀ n ζ, ζ ∈ poles n → ζ ∉ K) {f : ℂ → ℂ}
    (hlim : TendstoUniformlyOn
      (fun n z ↦ ∑ ζ ∈ poles n, coeff n ζ * (ζ - z)⁻¹)
      f atTop K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z ↦ Polynomial.eval z (q n))
        f atTop K := by
  classical
  apply exists_polynomial_tendstoUniformlyOn_of_iterated_limits K f
    (fun n z ↦ ∑ ζ ∈ poles n, coeff n ζ * (ζ - z)⁻¹) hlim
  intro n
  exact
    exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
      (poles n) (coeff n) id K hK hconvex (hpoles n)
