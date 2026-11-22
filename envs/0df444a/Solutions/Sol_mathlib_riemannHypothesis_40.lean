-- Prove2me | solution 40 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:55.23698+00:00
-- url     : https://prove2.me/submissions/1c4e2278-21ea-47dc-be7f-d955290a53fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_cofinal_signed_critical_band_certificates
import Theorems.Thm_MasulloRH_critical_zero_band_of_signed_brackets
import Theorems.Thm_MasulloRH_verified_square_prime_energy_prefix
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e3_1e4
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e4_1e5
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy

-- Step 1: `MasulloRH.cofinal_signed_critical_band_certificates` implies `MasulloRH.finite_square_prime_energy_cap` (accepted reduction of `MasulloRH.finite_square_prime_energy_cap`).
section

open MasulloRH Set Finset ArithmeticFunction MeasureTheory
private theorem critical_to_100000 (z : ZetaZerosInTraceStrip (1/2)) (hz : |z.val.im| ≤ 100000) :
    z.val.re = 1/2 := by
  have hpos (s : ℂ) (hs : riemannZeta s=0) (h0 : 0 < s.re) (h1 : s.re < 1)
      (him : 0 ≤ s.im) (hhigh : s.im ≤ 100000) : s.re=1/2 := by
    by_cases h2 : s.im ≤ 2
    · exact (ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six h0 h1
        (by rw [abs_of_nonneg him]; linarith) hs).elim
    by_cases h14 : s.im ≤ 14
    · exact (TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen s h0 h1 (by linarith) h14 hs).elim
    by_cases h100 : s.im ≤ 100
    · exact TaoFivePrimes.rh_verified_block_14_1e2 s hs h0 h1 (by linarith) (by norm_num; exact h100)
    by_cases h1k : s.im ≤ 1000
    · exact TaoFivePrimes.rh_verified_block_1e2_1e3 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact h1k)
    by_cases h10k : s.im ≤ 10000
    · exact TaoFivePrimes.rh_verified_block_1e3_1e4 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact h10k)
    exact TaoFivePrimes.rh_verified_block_1e4_1e5 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact hhigh)
  by_cases hr : 0 ≤ z.val.im
  · exact hpos z.val z.prop.1 z.prop.2.1 z.prop.2.2.1 hr ((le_abs_self _).trans hz)
  have hnot (j : ℕ) : z.val ≠ -j := by
    intro he; have h := congrArg Complex.re he; simp only [Complex.neg_re,Complex.natCast_re] at h
    linarith [z.prop.2.1,j.cast_nonneg (α:=ℝ)]
  have hnot1 : z.val ≠ 1 := by
    intro he; have h := congrArg Complex.re he; rw [Complex.one_re] at h; linarith [z.prop.2.2.1]
  have hzero : riemannZeta (1-z.val)=0 := by rw [riemannZeta_one_sub hnot hnot1,z.prop.1,mul_zero]
  have h := hpos (1-z.val) hzero (by simp; linarith [z.prop.2.2.1])
    (by simp; linarith [z.prop.2.1]) (by simp; linarith) (by simp; linarith [neg_le_abs z.val.im])
  simp at h
  linarith


private theorem height_budget (x : ℝ) (hx : 100 ≤ x) :
    2*(10+Real.log (x^4))*(x-97) ≤ 5/2+2*x^4-1 := by
  have hx0 : 0 < x := by linarith
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hlog := Real.log_le_sub_one_of_pos hx0
  have h1 : 2*(10+4*Real.log x)*(x-97) ≤ (12+8*x)*(x-97) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : (12+8*x)*(x-97) ≤ (12+8*x)*x :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 := mul_nonneg (sq_nonneg x) (by nlinarith : 0 ≤ 2*x^2-10)
  nlinarith

open Finset ArithmeticFunction MeasureTheory Set

theorem MasulloRH.finite_square_prime_energy_cap (N : ℕ) :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    (∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)) ≤ 81  := by
  let M : ℕ := (N+100)^4
  obtain ⟨H, hH, E, B, hE, hB, hD, hED, hcount⟩ :=
    cofinal_signed_critical_band_certificates (3+2*M)
  have hband := critical_zero_band_of_signed_brackets 100000 (H:ℝ) E B hE hB hD hED hcount
  have hcover (z : ZetaZerosInTraceStrip (1/2))
      (hz : |z.val.im| ≤ 5/2+2*(M:ℝ)) : z.val.re ≤ 1/2 := by
    by_cases hsmall : |z.val.im| ≤ 100000
    · exact (critical_to_100000 z hsmall).le
    · have hH' : (3:ℝ)+2*(M:ℝ) ≤ H := by exact_mod_cast hH
      exact (hband z (lt_of_not_ge hsmall) (by linarith)).le
  have hM : 1 ≤ M := by
    have hpos : 0 < M := by dsimp [M]; positivity
    omega
  have hbudget : 2*(10+Real.log M)*((N:ℝ)+3) ≤ 5/2+2*(M:ℝ)-1 := by
    have h := height_budget ((N:ℝ)+100) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
    simpa only [M, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
      show (N:ℝ)+100-97 = (N:ℝ)+3 by ring] using h
  have h := verified_square_prime_energy_prefix.2.2 M N hM hcover hbudget
  exact h.trans (by norm_num)

end

-- Step 2: `MasulloRH.finite_square_prime_energy_cap` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  by
  obtain ⟨-, h2, -⟩ := MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
  exact h2.mpr (fun N => MasulloRH.finite_square_prime_energy_cap N)

end
