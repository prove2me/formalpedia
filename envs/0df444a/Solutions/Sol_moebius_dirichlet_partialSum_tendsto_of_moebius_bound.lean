-- Prove2me | solution 1 for moebius_dirichlet_partialSum_tendsto_of_moebius_bound
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:38:37.251713+00:00
-- url     : https://prove2.me/submissions/26c76384-33b3-4805-b323-90fb088f25b6

import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

set_option autoImplicit false

open Finset Filter MeasureTheory Topology Asymptotics

/-- Abel summation: square-root-plus-epsilon growth of the Mertens function gives
convergence of the real Moebius Dirichlet series at every `σ > 1/2`. -/
theorem solution (σ : ℝ) (hσ : 1 / 2 < σ)
    (hM : ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds L) := by
  let r : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrs : r < σ := by dsimp [r]; linarith
  let c : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)
  have hc : c 0 = 0 := by simp [c]
  have hsum (N : ℕ) : ∑ k ∈ Icc 0 N, c k = ∑ k ∈ Icc 1 N, c k := by
    rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), hc]
    simp
  have hO : (fun N => ∑ k ∈ Icc 0 N, c k) =O[atTop] fun N => (N : ℝ) ^ r := by
    have h := hM ((σ - 1 / 2) / 2) (by linarith)
    have h' : (fun N => ((∑ k ∈ Icc 1 N, c k : ℝ) : ℂ)) =O[atTop]
        fun N => (N : ℝ) ^ r := by
      simpa [c, r, Complex.ofReal_sum] using h
    simpa only [hsum] using (Complex.isBigO_ofReal_left.mp h')
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-σ) * ∑ k ∈ Icc 0 N, c k)
      atTop (𝓝 0) := by
    have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(σ - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hrs)).comp tendsto_natCast_atTop_atTop
    exact (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-σ) r (-(σ - r))
      (isBigO_refl _ _) hO (by linarith)).trans_tendsto hp
  have hfloor : (fun t : ℝ => ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ r :=
    (hO.comp_tendsto tendsto_nat_floor_atTop).trans
      (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
  have hdom : (fun t : ℝ => deriv (fun x : ℝ => x ^ (-σ)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ (-σ - 1 + r) :=
    IsBigO.mul_atTop_rpow_of_isBigO_rpow (-σ - 1) r (-σ - 1 + r)
      (isBigO_deriv_rpow_const_atTop (-σ)) hfloor le_rfl
  have hint : LocallyIntegrableOn (deriv (fun x : ℝ => x ^ (-σ))) (Set.Ici 1) := by
    rw [Real.deriv_rpow_const']
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ici
    exact continuousOn_const.mul (fun t ht =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (zero_lt_one.trans_le ht).ne')).continuousWithinAt)
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc
    (f := fun x : ℝ => x ^ (-σ))
    (fun t ht => Real.differentiableAt_rpow_const_of_ne _ (zero_lt_one.trans_le ht).ne')
    hint hlim hdom (integrableAtFilter_rpow_atTop_iff.mpr (by linarith : -σ - 1 + r < -1))
  refine ⟨_, hconv.congr (fun N => ?_)⟩
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), hc, mul_zero, zero_add]
  simp only [zero_add]
  exact sum_congr rfl fun n _ => mul_comm _ _
