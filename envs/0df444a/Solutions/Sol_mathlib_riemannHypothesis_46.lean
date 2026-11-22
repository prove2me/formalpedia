-- Prove2me | solution 46 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:04.285443+00:00
-- url     : https://prove2.me/submissions/afcf4cd1-dc2a-4d19-a556-91405eacac9d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_real_certificate_has_rational_rounding
import Theorems.Thm_NymanBeurling_damped_moebius_mean_square_approximation
import Theorems.Thm_NymanBeurling_finite_remainder_zero_obstruction
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `NymanBeurling.damped_moebius_mean_square_approximation` implies `NymanBeurling.arbitrarily_small_remainder_certificates` (accepted reduction of `NymanBeurling.arbitrarily_small_remainder_certificates`).
section

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.arbitrarily_small_remainder_certificates (J : ℕ) :
    ∃ (c : ℕ →₀ ℚ) (H : ℕ), ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1/(J+1 : ℚ) := by
  classical
  let η : ℝ := 1 / (J+1 : ℝ)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, ε, hε, hεhalf, happrox⟩ :=
    NymanBeurling.damped_moebius_mean_square_approximation (η/2) (by positivity)
  let b : Fin N → ℝ := fun k => -((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε)
  let B : ℝ := (1 + ∑ k : Fin N, |b k|)^2
  obtain ⟨H, hH⟩ := exists_nat_gt (B / (η/2))
  have htail : B / (H+1 : ℝ) < η/2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < H+1)).2
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < η/2)).1 hH
    nlinarith
  have hfinite : (∑ n ∈ Finset.range H,
      (1 - ∑ k : Fin N, b k * (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) < η/2 := by
    simpa only [b, neg_mul, neg_div, Finset.sum_neg_distrib, sub_neg_eq_add] using happrox H
  obtain ⟨c, hc, hcost⟩ := NymanBeurling.real_certificate_has_rational_rounding N H b η
    (by change _ + B / (H+1 : ℝ) < η; linarith)
  refine ⟨c, H, ?_⟩
  apply (Rat.cast_lt (K := ℝ)).mp
  have hηcast : ((1 / (J+1 : ℚ) : ℚ) : ℝ) = η := by simp [η]
  rw [hηcast]
  exact hcost

end

-- Step 2: `NymanBeurling.arbitrarily_small_remainder_certificates` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

open scoped BigOperators

theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hpos : 0 < 2*s.re-1 := by linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt (‖s‖^2 / (2*s.re-1))
  obtain ⟨c,H,hC⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  let M : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
  change M < 1/(J+1 : ℚ) at hC
  have hc : (M:ℝ) < 1/(J+1:ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr hC
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast] using ht
  have hh := NymanBeurling.finite_remainder_zero_obstruction s hs hs_one hz c H
  change 2*s.re-1 ≤ (M:ℝ)*‖s‖^2 at hh
  apply (not_lt_of_ge hh)
  calc
    _ ≤ (1/(J+1:ℝ))*‖s‖^2 := mul_le_mul_of_nonneg_right hc.le (sq_nonneg _)
    _ < 2*s.re-1 := by
      rw [one_div,inv_mul_eq_div,div_lt_iff₀ (by positivity)]
      have hh := (div_lt_iff₀ hpos).mp hJ
      nlinarith

end

-- Step 3: `MasulloRH.zero_free_right` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => MasulloRH.zero_free_right s hs hs1
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n h => by
      have hre := congrArg Complex.re h
      simp at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hneg hs1
    rw [hz, mul_zero] at hfe
    have hre : (1 / 2 : ℝ) < (1 - s).re := by simp; linarith
    have h1s : (1 - s) ≠ 1 := fun h => by
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith
    exact hright (1 - s) hre h1s hfe
  · exact heq
  · exact absurd hz (hright s hgt hs1)

end
