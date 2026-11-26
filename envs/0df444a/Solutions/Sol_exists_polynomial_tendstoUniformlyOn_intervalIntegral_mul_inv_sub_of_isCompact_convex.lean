-- Prove2me | solution 1 for exists_polynomial_tendstoUniformlyOn_intervalIntegral_mul_inv_sub_of_isCompact_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:32.529958+00:00
-- url     : https://prove2.me/submissions/6c565120-37af-43bd-8ffa-b867c43b0654

import Definitions.Def_Operator_Crouzeix_ConvexRungeClosure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Theorems.Thm_exists_cauchyKernel_finset_tendstoUniformlyOn_setIntegral
import Theorems.Thm_exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex

section
open Complex Filter MeasureTheory Set
open scoped Topology Interval
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
open Complex Filter MeasureTheory Set
open scoped Topology Interval
theorem _root_.solution
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (coeff pole : ℝ → ℂ) (hcoeff : Continuous coeff)
    (hpole_cont : Continuous pole) (hpole : ∀ t, pole t ∉ K)
    {a b : ℝ} (hab : a < b) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z => Polynomial.eval z (q n))
        (fun z => ∫ t in a..b, coeff t * (pole t - z)⁻¹)
        atTop K := by
  obtain ⟨s, w, hquad⟩ :=
    exists_cauchyKernel_finset_tendstoUniformlyOn_setIntegral
      K hK coeff pole hcoeff hpole_cont hpole hab
  let g : ℕ → ℂ → ℂ := fun n z =>
    ∑ t ∈ s n, ((w n t : ℝ) : ℂ) * coeff t * (pole t - z)⁻¹
  have hquad' : TendstoUniformlyOn g
      (fun z => ∫ t in a..b, coeff t * (pole t - z)⁻¹) atTop K := by
    apply hquad.congr_right
    intro z _hz
    exact (intervalIntegral.integral_of_le hab.le).symm
  apply exists_polynomial_tendstoUniformlyOn_of_iterated_limits K
    (fun z => ∫ t in a..b, coeff t * (pole t - z)⁻¹) g hquad'
  intro n
  exact exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
    (s n) (fun t => ((w n t : ℝ) : ℂ) * coeff t)
      (fun t : Ioc a b => pole t)
      K hK hconvex (fun t _ht => hpole t)
