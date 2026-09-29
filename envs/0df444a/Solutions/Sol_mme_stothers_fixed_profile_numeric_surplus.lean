-- Prove2me | solution 1 for mme_stothers_fixed_profile_numeric_surplus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:03:27.847827+00:00
-- url     : https://prove2.me/submissions/567192e6-30f4-44ec-b556-4c09e73a6a17

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data

/-!
Verifier-ready, self-contained certificate for the exact Stothers q = 6
fixed profile. The helper declarations are bundled so that the Prove2Me
submission imports no unpublished research module.
-/

set_option autoImplicit false
set_option warningAsError true

/-! Bundled, audited source from research/agents/dwz_numeric_certificate/LogBounds.lean. -/

open Finset

namespace MME.DWZNumeric

/-!
Small, fully rigorous interval certificates for logarithms of rational
numbers.  The expansion used here is

  log ((1+x)/(1-x)) = 2 * sum_{i >= 0} x^(2i+1)/(2i+1).

`Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add` supply the
one-sided remainder bounds; all applications below reduce to rational
arithmetic with `norm_num`.
-/

noncomputable def logSeries (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)

theorem log_mem_Icc_of_ratio
    (q x lo hi : ℝ) (n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hq : q = (1 + x) / (1 - x))
    (hlo : lo ≤ 2 * logSeries x n)
    (hhi : 2 * (logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2)) ≤ hi) :
    lo ≤ Real.log q ∧ Real.log q ≤ hi := by
  have hL := Real.sum_range_le_log_div hx0 hx1 n
  have hU := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [← hq] at hL hU
  have hL' : logSeries x n ≤ 1 / 2 * Real.log q := by
    simpa [logSeries, Nat.cast_add, Nat.cast_mul] using hL
  have hU' : 1 / 2 * Real.log q ≤
      logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2) := by
    simpa [logSeries, Nat.cast_add, Nat.cast_mul] using hU
  constructor <;> nlinarith

/- A tight common interval for `log 2`. -/
theorem log_two_mem :
    (69314718055 / 100000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718057 / 100000000000 : ℝ) := by
  apply log_mem_Icc_of_ratio 2 (1 / 3) _ _ 12 <;>
    norm_num [logSeries, sum_range_succ]

theorem abs_log_div_log_two_sub_le_of_scaled
    (q r x c eps : ℝ) (k n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hratio : r = (1 + x) / (1 - x))
    (hq : q = r / (2 : ℝ) ^ k)
    (hrpos : 0 < r)
    (hd : 0 ≤ c + k - eps)
    (hlo : (c + k - eps) * (69314718057 / 100000000000 : ℝ) ≤
      2 * logSeries x n)
    (hhi : 2 * (logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2)) ≤
      (c + k + eps) * (69314718055 / 100000000000 : ℝ)) :
    |Real.log q / Real.log 2 - c| ≤ eps := by
  have htwo := log_two_mem
  have htwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := log_mem_Icc_of_ratio r x
    (2 * logSeries x n)
    (2 * (logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2))) n
    hx0 hx1 hratio le_rfl le_rfl
  have hscaled : Real.log q = Real.log r - (k : ℝ) * Real.log 2 := by
    rw [hq, Real.log_div hrpos.ne' (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne',
      Real.log_pow]
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ htwoPos]
    rw [hscaled]
    have hcoef : (c + k - eps) * Real.log 2 ≤
        (c + k - eps) * (69314718057 / 100000000000 : ℝ) :=
      mul_le_mul_of_nonneg_left htwo.2 hd
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ htwoPos]
    rw [hscaled]
    have hcoef : (c + k + eps) * (69314718055 / 100000000000 : ℝ) ≤
        (c + k + eps) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left htwo.1
      linarith
    nlinarith

end MME.DWZNumeric

/-! Bundled, audited source from research/missions/stothers_fourth_23737/proofs/NumericWitness.lean. -/

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-!
# An exact stationary witness for the Stothers `q = 6` endpoint

The displayed Table 2 decimals are rounded.  For the formal endpoint it is
enough to use the same distribution on both sides of Theorem 5.3.  The vector
below is a nearby exact rational stationary point.  All ten coordinates have
the common denominator `97942072`; this makes normalization, positivity, the
two stationary equations, and the zero kernel displacement decidable by
exact rational arithmetic.
-/

private def numericDen : ℕ := 97942072

/-- Exact positive frequency vector used for both `a` and `b` in the numeric
specialization of Theorem 5.3. -/
noncomputable def numericB : Fin 10 → ℝ :=
  ![(98 : ℝ) / numericDen,
    (1862 : ℝ) / numericDen,
    (73075 : ℝ) / numericDen,
    (1023050 : ℝ) / numericDen,
    (3626000 : ℝ) / numericDen,
    (98000 : ℝ) / numericDen,
    (2156000 : ℝ) / numericDen,
    (13720000 : ℝ) / numericDen,
    (21560000 : ℝ) / numericDen,
    (38710000 : ℝ) / numericDen]

theorem numericB_pos (i : Fin 10) : 0 < numericB i := by
  fin_cases i <;> norm_num [numericB, numericDen]

theorem numericB_mem_Z : InZ numericB := by
  constructor
  · intro i
    exact (numericB_pos i).le
  · norm_num [numericB, numericDen, classMultiplicity, Fin.sum_univ_succ]

theorem numericB_mem_N : InN numericB := by
  refine ⟨numericB_mem_Z, ?_, ?_⟩
  · change
      (73075 / numericDen : ℝ) * (13720000 / numericDen) ^ (2 : ℕ) =
        (3626000 / numericDen) * (98000 / numericDen) *
          (38710000 / numericDen)
    norm_num [numericDen]
  · change
      (1023050 / numericDen : ℝ) * (13720000 / numericDen) *
          (21560000 / numericDen) =
        (3626000 / numericDen) * (2156000 / numericDen) *
          (38710000 / numericDen)
    norm_num [numericDen]

theorem numericB_self_mem_Y :
    InY (fun i => numericB i - numericB i) := by
  refine ⟨0, 0, ?_⟩
  intro i
  simp

theorem numeric_tau_lower :
    (2 : ℝ) ≤ 3 * (23737 / 30000 : ℝ) := by
  norm_num

theorem numeric_tau_upper :
    3 * (23737 / 30000 : ℝ) ≤ (3 : ℝ) := by
  norm_num

/-- Equation (5.3) after specializing `a = b = numericB`.  The two internal
entropy factors cancel coordinatewise; only the ten constituent rates and the
nine marginal-entropy factors remain. -/
noncomputable def numericCoreRate (tau : ℝ) : ℝ :=
  (∏ i,
      (Real.rpow (classValue 6 tau i) (numericB i / 3)) ^
        classMultiplicity i) *
    ∏ j, Real.rpow (marginal numericB j) (-marginal numericB j)

theorem numeric_globalRate_eq (tau : ℝ) :
    globalRate 6 tau numericB numericB = numericCoreRate tau := by
  have hcancel (i : Fin 10) :
      Real.rpow (numericB i) (numericB i) *
          Real.rpow (numericB i) (-numericB i) = 1 := by
    change numericB i ^ numericB i * numericB i ^ (-numericB i) = 1
    rw [← Real.rpow_add (numericB_pos i)]
    simp
  unfold globalRate numericCoreRate
  congr 1
  apply Finset.prod_congr rfl
  intro i _hi
  rw [mul_assoc, hcancel, mul_one]

end MME.StothersFourth

/-! Bundled, audited source from research/missions/stothers_fourth_23737/proofs/NumericLogCertificates.lean. -/

open BigOperators Finset

namespace MME.StothersFourth.Numeric

set_option autoImplicit false

open MME.DWZNumeric

private theorem abs_log2_of_inv_cert
    (x c eps : ℝ)
    (h : |Real.log (1 / x) / Real.log 2 - (-c)| ≤ eps) :
    |Real.log x / Real.log 2 - c| ≤ eps := by
  rw [one_div, Real.log_inv] at h
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have heq :
      -Real.log x / Real.log 2 - -c =
        -(Real.log x / Real.log 2 - c) := by
    field_simp [hlog2]
    ring
  rw [heq, abs_neg] at h
  exact h

theorem log2_six_mem :
    |Real.log 6 / Real.log 2 - (25849625 / 10000000 : ℝ)| ≤
      1 / 100000000 := by
  apply abs_log2_of_inv_cert 6 (25849625 / 10000000)
    (1 / 100000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / 6) (r := 4 / 3) (x := 1 / 7)
    (c := -(25849625 / 10000000 : ℝ)) (eps := 1 / 100000000)
    (k := 3) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_twelve_mem :
    |Real.log 12 / Real.log 2 - (35849625 / 10000000 : ℝ)| ≤
      1 / 100000000 := by
  apply abs_log2_of_inv_cert 12 (35849625 / 10000000)
    (1 / 100000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / 12) (r := 4 / 3) (x := 1 / 7)
    (c := -(35849625 / 10000000 : ℝ)) (eps := 1 / 100000000)
    (k := 4) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_thirty_eight_mem :
    |Real.log 38 / Real.log 2 - (524792751 / 100000000 : ℝ)| ≤
      1 / 100000000 := by
  apply abs_log2_of_inv_cert 38 (524792751 / 100000000)
    (1 / 100000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / 38) (r := 32 / 19) (x := 13 / 51)
    (c := -(524792751 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 6) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_twenty_four_mem :
    |Real.log 24 / Real.log 2 - (45849625 / 10000000 : ℝ)| ≤
      1 / 100000000 := by
  apply abs_log2_of_inv_cert 24 (45849625 / 10000000)
    (1 / 100000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / 24) (r := 4 / 3) (x := 1 / 7)
    (c := -(45849625 / 10000000 : ℝ)) (eps := 1 / 100000000)
    (k := 5) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_two_twenty_mem :
    |Real.log 220 / Real.log 2 - (778135971 / 100000000 : ℝ)| ≤
      1 / 100000000 := by
  apply abs_log2_of_inv_cert 220 (778135971 / 100000000)
    (1 / 100000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / 220) (r := 64 / 55) (x := 9 / 119)
    (c := -(778135971 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 8) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_nine_thirty_six_mem :
    |Real.log 936 / Real.log 2 - (987036472 / 100000000 : ℝ)| ≤
      1 / 100000000 := by
  apply abs_log2_of_inv_cert 936 (987036472 / 100000000)
    (1 / 100000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / 936) (r := 128 / 117) (x := 11 / 245)
    (c := -(987036472 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 10) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_seventeen_thirty_four_mem :
    |Real.log 1734 / Real.log 2 - (1075988818 / 100000000 : ℝ)| ≤
      1 / 100000000 := by
  apply abs_log2_of_inv_cert 1734 (1075988818 / 100000000)
    (1 / 100000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / 1734) (r := 1024 / 867) (x := 157 / 1891)
    (c := -(1075988818 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 11) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_p_lower_mem :
    |Real.log (70323 / 1000 : ℝ) / Real.log 2 -
        (613592471 / 100000000 : ℝ)| ≤ 1 / 100000000 := by
  apply abs_log2_of_inv_cert (70323 / 1000) (613592471 / 100000000)
    (1 / 100000000)
  rw [show (1 / (70323 / 1000 : ℝ)) = 1000 / 70323 by norm_num]
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1000 / 70323) (r := 128000 / 70323) (x := 57677 / 198323)
    (c := -(613592471 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 7) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_p_upper_mem :
    |Real.log (70324 / 1000 : ℝ) / Real.log 2 -
        (613594523 / 100000000 : ℝ)| ≤ 1 / 100000000 := by
  apply abs_log2_of_inv_cert (70324 / 1000) (613594523 / 100000000)
    (1 / 100000000)
  rw [show (1 / (70324 / 1000 : ℝ)) = 1000 / 70324 by norm_num]
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1000 / 70324) (r := 32000 / 17581) (x := 14419 / 49581)
    (c := -(613594523 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 7) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_e_lower_mem :
    |Real.log (364462 / 1000 : ℝ) / Real.log 2 -
        (850962459 / 100000000 : ℝ)| ≤ 1 / 100000000 := by
  apply abs_log2_of_inv_cert (364462 / 1000) (850962459 / 100000000)
    (1 / 100000000)
  rw [show (1 / (364462 / 1000 : ℝ)) = 1000 / 364462 by norm_num]
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1000 / 364462) (r := 256000 / 182231) (x := 73769 / 438231)
    (c := -(850962459 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 9) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_e_upper_mem :
    |Real.log (364463 / 1000 : ℝ) / Real.log 2 -
        (850962855 / 100000000 : ℝ)| ≤ 1 / 100000000 := by
  apply abs_log2_of_inv_cert (364463 / 1000) (850962855 / 100000000)
    (1 / 100000000)
  rw [show (1 / (364463 / 1000 : ℝ)) = 1000 / 364463 by norm_num]
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1000 / 364463) (r := 512000 / 364463) (x := 147537 / 876463)
    (c := -(850962855 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 9) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_h_lower_mem :
    |Real.log (562253 / 100 : ℝ) / Real.log 2 -
        (1245700374 / 100000000 : ℝ)| ≤ 1 / 100000000 := by
  apply abs_log2_of_inv_cert (562253 / 100) (1245700374 / 100000000)
    (1 / 100000000)
  rw [show (1 / (562253 / 100 : ℝ)) = 100 / 562253 by norm_num]
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 100 / 562253) (r := 819200 / 562253) (x := 256947 / 1381453)
    (c := -(1245700374 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 13) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

theorem log2_h_upper_mem :
    |Real.log (562254 / 100 : ℝ) / Real.log 2 -
        (1245700630 / 100000000 : ℝ)| ≤ 1 / 100000000 := by
  apply abs_log2_of_inv_cert (562254 / 100) (1245700630 / 100000000)
    (1 / 100000000)
  rw [show (1 / (562254 / 100 : ℝ)) = 100 / 562254 by norm_num]
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 100 / 562254) (r := 409600 / 281127) (x := 128473 / 690727)
    (c := -(1245700630 / 100000000 : ℝ)) (eps := 1 / 100000000)
    (k := 13) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

/-! ## Rational lower surrogates for the five recursive class values -/

noncomputable def class5Lower : ℝ := 43380078019 / 62500

noncomputable def class6Lower : ℝ :=
  255369741195401817311 / 5490761718750

noncomputable def class7Lower : ℝ :=
  16446188334301683 / 31250000

noncomputable def class8Lower : ℝ :=
  66040263730608890675039069 / 58568125000000000

noncomputable def class9Lower : ℝ :=
  211663420364619791011159707289 / 79470515250000000000

theorem log2_class5Lower_mem :
    |Real.log class5Lower / Real.log 2 -
        (1940474503 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log2_of_inv_cert class5Lower (1940474503 / 100000000)
    (1 / 10000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / class5Lower) (r := 65536000000 / 43380078019)
    (x := 22155921981 / 108916078019)
    (c := -(1940474503 / 100000000 : ℝ)) (eps := 1 / 10000000)
    (k := 20) (n := 12) <;>
    norm_num [class5Lower, logSeries, sum_range_succ]

theorem log2_class6Lower_mem :
    |Real.log class6Lower / Real.log 2 -
        (636775151 / 25000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log2_of_inv_cert class6Lower (636775151 / 25000000)
    (1 / 10000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / class6Lower)
    (r := 368478781440000000000 / 255369741195401817311)
    (x := 113109040244598182689 / 623848522635401817311)
    (c := -(636775151 / 25000000 : ℝ)) (eps := 1 / 10000000)
    (k := 26) (n := 12) <;>
    norm_num [class6Lower, logSeries, sum_range_succ]

theorem log2_class7Lower_mem :
    |Real.log class7Lower / Real.log 2 -
        (22633789 / 781250 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log2_of_inv_cert class7Lower (22633789 / 781250)
    (1 / 10000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / class7Lower)
    (r := 16777216000000000 / 16446188334301683)
    (x := 331027665698317 / 33223404334301683)
    (c := -(22633789 / 781250 : ℝ)) (eps := 1 / 10000000)
    (k := 29) (n := 12) <;>
    norm_num [class7Lower, logSeries, sum_range_succ]

theorem log2_class8Lower_mem :
    |Real.log class8Lower / Real.log 2 -
        (3007058303 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log2_of_inv_cert class8Lower (3007058303 / 100000000)
    (1 / 10000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / class8Lower)
    (r := 125774090731520000000000000 /
      66040263730608890675039069)
    (x := 59733827000911109324960931 /
      191814354462128890675039069)
    (c := -(3007058303 / 100000000 : ℝ)) (eps := 1 / 10000000)
    (k := 31) (n := 12) <;>
    norm_num [class8Lower, logSeries, sum_range_succ]

theorem log2_class9Lower_mem :
    |Real.log class9Lower / Real.log 2 -
        (1565531661 / 50000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log2_of_inv_cert class9Lower (1565531661 / 50000000)
    (1 / 10000000)
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1 / class9Lower)
    (r := 341323263995019264000000000000 /
      211663420364619791011159707289)
    (x := 129659843630399472988840292711 /
      552986684359639055011159707289)
    (c := -(1565531661 / 50000000 : ℝ)) (eps := 1 / 10000000)
    (k := 32) (n := 12) <;>
    norm_num [class9Lower, logSeries, sum_range_succ]

/-! ## The nine exact marginals of `numericB` -/

noncomputable def numericMarginal : Fin 9 → ℝ :=
  ![(2911085 : ℝ) / 146913108,
    (7987931 : ℝ) / 73456554,
    (43144075 : ℝ) / 146913108,
    (26726525 : ℝ) / 73456554,
    (7031500 : ℝ) / 36728277,
    (1589525 : ℝ) / 73456554,
    (122075 : ℝ) / 146913108,
    (931 : ℝ) / 73456554,
    (49 : ℝ) / 146913108]

private theorem marginal0_log_mem :
    |Real.log (2911085 / 146913108 : ℝ) / Real.log 2 -
        (-113145247 / 20000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 2911085 / 146913108) (r := 46577360 / 36728277)
    (x := 9849083 / 83305637)
    (c := -113145247 / 20000000) (eps := 1 / 10000000)
    (k := 6) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal1_log_mem :
    |Real.log (7987931 / 73456554 : ℝ) / Real.log 2 -
        (-10003117 / 3125000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 7987931 / 73456554) (r := 63903448 / 36728277)
    (x := 27175171 / 100631725)
    (c := -10003117 / 3125000) (eps := 1 / 10000000)
    (k := 4) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal2_log_mem :
    |Real.log (43144075 / 146913108 : ℝ) / Real.log 2 -
        (-176772877 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 43144075 / 146913108) (r := 43144075 / 36728277)
    (x := 3207899 / 39936176)
    (c := -176772877 / 100000000) (eps := 1 / 10000000)
    (k := 2) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal3_log_mem :
    |Real.log (26726525 / 73456554 : ℝ) / Real.log 2 -
        (-29172379 / 20000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 26726525 / 73456554) (r := 53453050 / 36728277)
    (x := 16724773 / 90181327)
    (c := -29172379 / 20000000) (eps := 1 / 10000000)
    (k := 2) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal4_log_mem :
    |Real.log (7031500 / 36728277 : ℝ) / Real.log 2 -
        (-238498683 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 7031500 / 36728277) (r := 56252000 / 36728277)
    (x := 19523723 / 92980277)
    (c := -238498683 / 100000000) (eps := 1 / 10000000)
    (k := 3) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal5_log_mem :
    |Real.log (1589525 / 73456554 : ℝ) / Real.log 2 -
        (-553022361 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1589525 / 73456554) (r := 50864800 / 36728277)
    (x := 14136523 / 87593077)
    (c := -553022361 / 100000000) (eps := 1 / 10000000)
    (k := 6) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal6_log_mem :
    |Real.log (122075 / 146913108 : ℝ) / Real.log 2 -
        (-1023297963 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 122075 / 146913108) (r := 62502400 / 36728277)
    (x := 25774123 / 99230677)
    (c := -1023297963 / 100000000) (eps := 1 / 10000000)
    (k := 11) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal7_log_mem :
    |Real.log (931 / 73456554 : ℝ) / Real.log 2 -
        (-406693763 / 25000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 931 / 73456554) (r := 61014016 / 36728277)
    (x := 24285739 / 97742293)
    (c := -406693763 / 25000000) (eps := 1 / 10000000)
    (k := 17) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

private theorem marginal8_log_mem :
    |Real.log (49 / 146913108 : ℝ) / Real.log 2 -
        (-537891951 / 25000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 49 / 146913108) (r := 51380224 / 36728277)
    (x := 14651947 / 88108501)
    (c := -537891951 / 25000000) (eps := 1 / 10000000)
    (k := 22) (n := 12) <;>
    norm_num [logSeries, sum_range_succ]

noncomputable def marginalLogCenter : Fin 9 → ℝ :=
  ![-113145247 / 20000000,
    -10003117 / 3125000,
    -176772877 / 100000000,
    -29172379 / 20000000,
    -238498683 / 100000000,
    -553022361 / 100000000,
    -1023297963 / 100000000,
    -406693763 / 25000000,
    -537891951 / 25000000]

theorem numericMarginal_log_mem (j : Fin 9) :
    |Real.log (numericMarginal j) / Real.log 2 - marginalLogCenter j| ≤
      1 / 10000000 := by
  fin_cases j
  · simpa [numericMarginal, marginalLogCenter] using marginal0_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal1_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal2_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal3_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal4_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal5_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal6_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal7_log_mem
  · simpa [numericMarginal, marginalLogCenter] using marginal8_log_mem

end MME.StothersFourth.Numeric

/-! Bundled, audited source from research/missions/stothers_fourth_23737/proofs/numeric_finish/Bounds.lean. -/

open MME BigOperators Finset

namespace MME.StothersFourth.NumericFinish

set_option autoImplicit false
set_option warningAsError true

noncomputable def tau0 : ℝ := 23737 / 30000
noncomputable def rho0 : ℝ := 23737 / 10000

noncomputable def pLower : ℝ := 70323 / 1000
noncomputable def pUpper : ℝ := 70324 / 1000
noncomputable def eLower : ℝ := 364462 / 1000
noncomputable def eUpper : ℝ := 364463 / 1000
noncomputable def hLower : ℝ := 562253 / 100
noncomputable def hUpper : ℝ := 562254 / 100
noncomputable def lLower : ℝ := 5085970329 / 250000
noncomputable def lUpper : ℝ := 317882061 / 15625

private theorem log2_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

private theorem div_log2_lt_gives_lt
    {x y : ℝ} (h : x / Real.log 2 < y / Real.log 2) : x < y :=
  (div_lt_div_iff_of_pos_right log2_pos).mp h

private theorem lower_lt_rpow_of_log_certs
    (x base rho xCenter baseCenter xEps baseEps : ℝ)
    (hx : 0 < x) (hbase : 0 < base) (hrho : 0 < rho)
    (hxCert :
      |Real.log x / Real.log 2 - xCenter| ≤ xEps)
    (hbaseCert :
      |Real.log base / Real.log 2 - baseCenter| ≤ baseEps)
    (hgap : xCenter + xEps < rho * (baseCenter - baseEps)) :
    x < base ^ rho := by
  rw [Real.lt_rpow_iff_log_lt hx hbase]
  have hxUpper := (abs_le.mp hxCert).2
  have hbaseLower := (abs_le.mp hbaseCert).1
  have hbaseLower' :
      baseCenter - baseEps ≤ Real.log base / Real.log 2 := by
    linarith
  have hxUpper' :
      Real.log x / Real.log 2 ≤ xCenter + xEps := by
    linarith
  have hratio :
      Real.log x / Real.log 2 <
        rho * (Real.log base / Real.log 2) :=
    hxUpper'.trans_lt
      (hgap.trans_le (mul_le_mul_of_nonneg_left hbaseLower' hrho.le))
  have hratio' :
      Real.log x / Real.log 2 <
        (rho * Real.log base) / Real.log 2 := by
    convert hratio using 1
    field_simp [log2_pos.ne']
  exact div_log2_lt_gives_lt hratio'

private theorem rpow_lt_upper_of_log_certs
    (base rho x baseCenter xCenter baseEps xEps : ℝ)
    (hbase : 0 < base) (hrho : 0 < rho) (hx : 0 < x)
    (hbaseCert :
      |Real.log base / Real.log 2 - baseCenter| ≤ baseEps)
    (hxCert :
      |Real.log x / Real.log 2 - xCenter| ≤ xEps)
    (hgap : rho * (baseCenter + baseEps) < xCenter - xEps) :
    base ^ rho < x := by
  have hbaseUpper := (abs_le.mp hbaseCert).2
  have hxLower := (abs_le.mp hxCert).1
  have hxLower' :
      xCenter - xEps ≤ Real.log x / Real.log 2 := by
    linarith
  have hbaseUpper' :
      Real.log base / Real.log 2 ≤ baseCenter + baseEps := by
    linarith
  have hratio :
      rho * (Real.log base / Real.log 2) <
        Real.log x / Real.log 2 :=
    (mul_le_mul_of_nonneg_left
      hbaseUpper' hrho.le).trans_lt
      (hgap.trans_le hxLower')
  have hratio' :
      (rho * Real.log base) / Real.log 2 <
        Real.log x / Real.log 2 := by
    convert hratio using 1
    field_simp [log2_pos.ne']
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hbase _)
    hx).mp
  rw [Real.log_rpow hbase]
  exact div_log2_lt_gives_lt hratio'

theorem pLower_lt_p : pLower < (6 : ℝ) ^ rho0 := by
  apply lower_lt_rpow_of_log_certs
    pLower 6 rho0 (613592471 / 100000000)
      (25849625 / 10000000) (1 / 100000000) (1 / 100000000)
  · norm_num [pLower]
  · norm_num
  · norm_num [rho0]
  · exact Numeric.log2_p_lower_mem
  · exact Numeric.log2_six_mem
  · norm_num [rho0]

theorem p_lt_pUpper : (6 : ℝ) ^ rho0 < pUpper := by
  apply rpow_lt_upper_of_log_certs
    6 rho0 pUpper (25849625 / 10000000)
      (613594523 / 100000000) (1 / 100000000) (1 / 100000000)
  · norm_num
  · norm_num [rho0]
  · norm_num [pUpper]
  · exact Numeric.log2_six_mem
  · exact Numeric.log2_p_upper_mem
  · norm_num [rho0]

theorem eLower_lt_e : eLower < (12 : ℝ) ^ rho0 := by
  apply lower_lt_rpow_of_log_certs
    eLower 12 rho0 (850962459 / 100000000)
      (35849625 / 10000000) (1 / 100000000) (1 / 100000000)
  · norm_num [eLower]
  · norm_num
  · norm_num [rho0]
  · exact Numeric.log2_e_lower_mem
  · exact Numeric.log2_twelve_mem
  · norm_num [rho0]

theorem e_lt_eUpper : (12 : ℝ) ^ rho0 < eUpper := by
  apply rpow_lt_upper_of_log_certs
    12 rho0 eUpper (35849625 / 10000000)
      (850962855 / 100000000) (1 / 100000000) (1 / 100000000)
  · norm_num
  · norm_num [rho0]
  · norm_num [eUpper]
  · exact Numeric.log2_twelve_mem
  · exact Numeric.log2_e_upper_mem
  · norm_num [rho0]

theorem hLower_lt_h : hLower < (38 : ℝ) ^ rho0 := by
  apply lower_lt_rpow_of_log_certs
    hLower 38 rho0 (1245700374 / 100000000)
      (524792751 / 100000000) (1 / 100000000) (1 / 100000000)
  · norm_num [hLower]
  · norm_num
  · norm_num [rho0]
  · exact Numeric.log2_h_lower_mem
  · exact Numeric.log2_thirty_eight_mem
  · norm_num [rho0]

theorem h_lt_hUpper : (38 : ℝ) ^ rho0 < hUpper := by
  apply rpow_lt_upper_of_log_certs
    38 rho0 hUpper (524792751 / 100000000)
      (1245700630 / 100000000) (1 / 100000000) (1 / 100000000)
  · norm_num
  · norm_num [rho0]
  · norm_num [hUpper]
  · exact Numeric.log2_thirty_eight_mem
  · exact Numeric.log2_h_upper_mem
  · norm_num [rho0]

theorem lLower_lt_l :
    lLower < 4 * (6 : ℝ) ^ rho0 * ((6 : ℝ) ^ rho0 + 2) := by
  have hp := pLower_lt_p
  have hp0 : 0 < (6 : ℝ) ^ rho0 := Real.rpow_pos_of_pos (by norm_num) _
  calc
    lLower = 4 * pLower * (pLower + 2) := by
      norm_num [lLower, pLower]
    _ < 4 * (6 : ℝ) ^ rho0 * (pLower + 2) := by
      gcongr
      norm_num [pLower]
    _ < 4 * (6 : ℝ) ^ rho0 * ((6 : ℝ) ^ rho0 + 2) := by
      gcongr

theorem l_lt_lUpper :
    4 * (6 : ℝ) ^ rho0 * ((6 : ℝ) ^ rho0 + 2) < lUpper := by
  have hp := p_lt_pUpper
  have hp0 : 0 < (6 : ℝ) ^ rho0 := Real.rpow_pos_of_pos (by norm_num) _
  calc
    4 * (6 : ℝ) ^ rho0 * ((6 : ℝ) ^ rho0 + 2) <
        4 * pUpper * ((6 : ℝ) ^ rho0 + 2) := by
      gcongr
    _ < 4 * pUpper * (pUpper + 2) := by
      gcongr
      norm_num [pUpper]
    _ = lUpper := by
      norm_num [lUpper, pUpper]

private theorem three_tau0_eq_rho0 : 3 * tau0 = rho0 := by
  norm_num [tau0, rho0]

theorem E_lower : eLower < E 6 tau0 := by
  change eLower < (12 : ℝ) ^ (3 * tau0)
  rw [three_tau0_eq_rho0]
  exact eLower_lt_e

theorem E_upper : E 6 tau0 < eUpper := by
  change (12 : ℝ) ^ (3 * tau0) < eUpper
  rw [three_tau0_eq_rho0]
  exact e_lt_eUpper

theorem H_lower : hLower < H 6 tau0 := by
  change hLower < ((6 : ℝ) ^ (2 : ℕ) + 2) ^ (3 * tau0)
  norm_num only [show (6 : ℝ) ^ (2 : ℕ) + 2 = 38 by norm_num]
  rw [three_tau0_eq_rho0]
  exact hLower_lt_h

theorem H_upper : H 6 tau0 < hUpper := by
  change ((6 : ℝ) ^ (2 : ℕ) + 2) ^ (3 * tau0) < hUpper
  norm_num only [show (6 : ℝ) ^ (2 : ℕ) + 2 = 38 by norm_num]
  rw [three_tau0_eq_rho0]
  exact h_lt_hUpper

theorem L_lower : lLower < L 6 tau0 := by
  change lLower <
    4 * (6 : ℝ) ^ (3 * tau0) * ((6 : ℝ) ^ (3 * tau0) + 2)
  rw [three_tau0_eq_rho0]
  exact lLower_lt_l

theorem L_upper : L 6 tau0 < lUpper := by
  change
    4 * (6 : ℝ) ^ (3 * tau0) * ((6 : ℝ) ^ (3 * tau0) + 2) <
      lUpper
  rw [three_tau0_eq_rho0]
  exact l_lt_lUpper

theorem classValue_pos (i : Fin 10) : 0 < classValue 6 tau0 i := by
  fin_cases i <;>
    simp [classValue, E, H, L, tau0] <;> positivity

/-- The five recursive Table-1 constituents are strictly above the exact
rational surrogates whose logarithms are certified in
`NumericLogCertificates`. -/
theorem class5Lower_lt_classValue :
    Numeric.class5Lower < classValue 6 tau0 5 := by
  have hE := E_lower
  have hL := L_lower
  have hE0 : 0 < E 6 tau0 := by unfold E; positivity
  have heLower0 : 0 ≤ eLower := by norm_num [eLower]
  calc
    Numeric.class5Lower =
        4 * (eLower ^ (2 : ℕ) + 2 * lLower) := by
      norm_num [Numeric.class5Lower, eLower, lLower]
    _ < 4 * (E 6 tau0 ^ (2 : ℕ) + 2 * L 6 tau0) := by
      gcongr
    _ = classValue 6 tau0 5 := by
      simp [classValue]

theorem class6Lower_lt_classValue :
    Numeric.class6Lower < classValue 6 tau0 6 := by
  have hE := E_lower
  have hH := H_lower
  have hH' := H_upper
  have hL := L_lower
  have hE0 : 0 < E 6 tau0 := by unfold E; positivity
  have hH0 : 0 < H 6 tau0 := by unfold H; positivity
  have hL0 : 0 < L 6 tau0 := by unfold L; positivity
  have heLower0 : 0 ≤ eLower := by norm_num [eLower]
  have hhLower0 : 0 ≤ hLower := by norm_num [hLower]
  have hlLower0 : 0 ≤ lLower := by norm_num [lLower]
  calc
    Numeric.class6Lower =
        4 * (lLower + eLower * hLower) *
          (2 * hLower + lLower) / hUpper := by
      norm_num [Numeric.class6Lower, eLower, hLower, hUpper, lLower]
    _ < 4 * (L 6 tau0 + E 6 tau0 * H 6 tau0) *
          (2 * H 6 tau0 + L 6 tau0) / H 6 tau0 := by
      gcongr
    _ = classValue 6 tau0 6 := by
      simp [classValue]

theorem class7Lower_lt_classValue :
    Numeric.class7Lower < classValue 6 tau0 7 := by
  have hE := E_lower
  have hH := H_lower
  have hL := L_lower
  have hE0 : 0 < E 6 tau0 := by unfold E; positivity
  have hH0 : 0 < H 6 tau0 := by unfold H; positivity
  have hL0 : 0 < L 6 tau0 := by unfold L; positivity
  have heLower0 : 0 ≤ eLower := by norm_num [eLower]
  have hhLower0 : 0 ≤ hLower := by norm_num [hLower]
  have hlLower0 : 0 ≤ lLower := by norm_num [lLower]
  calc
    Numeric.class7Lower =
        4 * (eLower + lLower) * (2 + 2 * eLower + hLower) := by
      norm_num [Numeric.class7Lower, eLower, hLower, lLower]
    _ < 4 * (E 6 tau0 + L 6 tau0) *
          (2 + 2 * E 6 tau0 + H 6 tau0) := by
      gcongr
    _ = classValue 6 tau0 7 := by
      simp [classValue]

theorem class8Lower_lt_classValue :
    Numeric.class8Lower < classValue 6 tau0 8 := by
  have hE := E_lower
  have hH := H_lower
  have hH' := H_upper
  have hL := L_lower
  have hE0 : 0 < E 6 tau0 := by unfold E; positivity
  have hH0 : 0 < H 6 tau0 := by unfold H; positivity
  have hL0 : 0 < L 6 tau0 := by unfold L; positivity
  have heLower0 : 0 ≤ eLower := by norm_num [eLower]
  have hhLower0 : 0 ≤ hLower := by norm_num [hLower]
  have hlLower0 : 0 ≤ lLower := by norm_num [lLower]
  calc
    Numeric.class8Lower =
        (2 * hLower + lLower) ^ (2 : ℕ) *
          (2 + 2 * eLower + hLower) / hUpper := by
      norm_num [Numeric.class8Lower, eLower, hLower, hUpper, lLower]
    _ < (2 * H 6 tau0 + L 6 tau0) ^ (2 : ℕ) *
          (2 + 2 * E 6 tau0 + H 6 tau0) / H 6 tau0 := by
      gcongr
    _ = classValue 6 tau0 8 := by
      simp [classValue]

theorem class9Lower_lt_classValue :
    Numeric.class9Lower < classValue 6 tau0 9 := by
  have hE := E_lower
  have hH := H_lower
  have hL := L_lower
  have hL' := L_upper
  have hE0 : 0 < E 6 tau0 := by unfold E; positivity
  have hH0 : 0 < H 6 tau0 := by unfold H; positivity
  have hL0 : 0 < L 6 tau0 := by unfold L; positivity
  have heLower0 : 0 ≤ eLower := by norm_num [eLower]
  have hhLower0 : 0 ≤ hLower := by norm_num [hLower]
  have hlLower0 : 0 ≤ lLower := by norm_num [lLower]
  calc
    Numeric.class9Lower =
        4 * (eLower + lLower) ^ (2 : ℕ) *
          (2 * hLower + lLower) / lUpper := by
      norm_num [Numeric.class9Lower, eLower, hLower, lLower, lUpper]
    _ < 4 * (E 6 tau0 + L 6 tau0) ^ (2 : ℕ) *
          (2 * H 6 tau0 + L 6 tau0) / L 6 tau0 := by
      gcongr
    _ = classValue 6 tau0 9 := by
      simp [classValue]

/-- The exact nine marginals of the fixed rational frequency vector. -/
theorem numericB_explicit :
    numericB =
      ![(98 : ℝ) / 97942072,
        (1862 : ℝ) / 97942072,
        (73075 : ℝ) / 97942072,
        (1023050 : ℝ) / 97942072,
        (3626000 : ℝ) / 97942072,
        (98000 : ℝ) / 97942072,
        (2156000 : ℝ) / 97942072,
        (13720000 : ℝ) / 97942072,
        (21560000 : ℝ) / 97942072,
        (38710000 : ℝ) / 97942072] := by
  rfl

theorem marginal_numericB_eq (j : Fin 9) :
    marginal numericB j = Numeric.numericMarginal j := by
  rw [numericB_explicit]
  fin_cases j <;>
    simp [marginal, Q, Numeric.numericMarginal] <;> norm_num

theorem numericMarginal_pos (j : Fin 9) :
    0 < Numeric.numericMarginal j := by
  fin_cases j <;> norm_num [Numeric.numericMarginal]

end MME.StothersFourth.NumericFinish

/-! Bundled, audited source from research/missions/stothers_fourth_23737/proofs/numeric_finish/ScalarRate.lean. -/

open MME BigOperators Finset

namespace MME.StothersFourth.NumericFinish

set_option autoImplicit false
set_option warningAsError true

private theorem scalar_log2_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

/-- Coordinatewise lower bounds for the base-two logarithms of all ten
Table-1 class values.  Coordinate zero is exact. -/
noncomputable def classLogLower : Fin 10 → ℝ :=
  ![0,
    rho0 * (45849625 / 10000000 - 1 / 100000000),
    rho0 * (778135971 / 100000000 - 1 / 100000000),
    rho0 * (987036472 / 100000000 - 1 / 100000000),
    rho0 * (1075988818 / 100000000 - 1 / 100000000),
    1940474503 / 100000000 - 1 / 10000000,
    636775151 / 25000000 - 1 / 10000000,
    22633789 / 781250 - 1 / 10000000,
    3007058303 / 100000000 - 1 / 10000000,
    1565531661 / 50000000 - 1 / 10000000]

/-- Coordinatewise upper bounds for the base-two logarithms of the nine
exact marginals.  Multiplication by `-marginal` turns these into lower entropy
bounds. -/
noncomputable def marginalLogUpper : Fin 9 → ℝ := fun j ↦
  Numeric.marginalLogCenter j + 1 / 10000000

private theorem rho_log_lower
    (base center eps : ℝ) (hbase : 0 < base)
    (hcert :
      |Real.log base / Real.log 2 - center| ≤ eps) :
    rho0 * (center - eps) ≤
      Real.log (base ^ rho0) / Real.log 2 := by
  have hlower : center - eps ≤ Real.log base / Real.log 2 := by
    have := (abs_le.mp hcert).1
    linarith
  rw [Real.log_rpow hbase]
  calc
    rho0 * (center - eps) ≤
        rho0 * (Real.log base / Real.log 2) :=
      mul_le_mul_of_nonneg_left hlower (by norm_num [rho0])
    _ = (rho0 * Real.log base) / Real.log 2 := by
      field_simp [scalar_log2_pos.ne']

private theorem lower_log_of_lt
    (lower value center eps : ℝ)
    (hlower : 0 < lower) (hlt : lower < value)
    (hcert :
      |Real.log lower / Real.log 2 - center| ≤ eps) :
    center - eps ≤ Real.log value / Real.log 2 := by
  have hcertLower :
      center - eps ≤ Real.log lower / Real.log 2 := by
    have := (abs_le.mp hcert).1
    linarith
  have hlog : Real.log lower < Real.log value :=
    Real.log_lt_log hlower hlt
  have hratio :
      Real.log lower / Real.log 2 < Real.log value / Real.log 2 :=
    (div_lt_div_iff_of_pos_right scalar_log2_pos).2 hlog
  exact hcertLower.trans hratio.le

theorem classLogLower_le (i : Fin 10) :
    classLogLower i ≤
      Real.log (classValue 6 tau0 i) / Real.log 2 := by
  fin_cases i
  · norm_num [classLogLower, classValue]
  · change rho0 * (45849625 / 10000000 - 1 / 100000000) ≤
      Real.log ((4 * 6 : ℝ) ^ (3 * tau0)) / Real.log 2
    norm_num only [show (4 * 6 : ℝ) = 24 by norm_num]
    rw [show 3 * tau0 = rho0 by norm_num [tau0, rho0]]
    have h := rho_log_lower 24 (45849625 / 10000000) (1 / 100000000)
      (by norm_num) Numeric.log2_twenty_four_mem
    norm_num at h ⊢
    exact h
  · change rho0 * (778135971 / 100000000 - 1 / 100000000) ≤
      Real.log ((6 * 6 ^ (2 : ℕ) + 4 : ℝ) ^ (3 * tau0)) /
        Real.log 2
    norm_num only [show (6 * 6 ^ (2 : ℕ) + 4 : ℝ) = 220 by norm_num]
    rw [show 3 * tau0 = rho0 by norm_num [tau0, rho0]]
    have h := rho_log_lower 220 (778135971 / 100000000) (1 / 100000000)
      (by norm_num) Numeric.log2_two_twenty_mem
    norm_num at h ⊢
    exact h
  · change rho0 * (987036472 / 100000000 - 1 / 100000000) ≤
      Real.log ((4 * 6 * (6 ^ (2 : ℕ) + 3) : ℝ) ^ (3 * tau0)) /
        Real.log 2
    norm_num only [show (4 * 6 * (6 ^ (2 : ℕ) + 3) : ℝ) = 936 by norm_num]
    rw [show 3 * tau0 = rho0 by norm_num [tau0, rho0]]
    have h := rho_log_lower 936 (987036472 / 100000000) (1 / 100000000)
      (by norm_num) Numeric.log2_nine_thirty_six_mem
    norm_num at h ⊢
    exact h
  · change rho0 * (1075988818 / 100000000 - 1 / 100000000) ≤
      Real.log ((6 ^ (4 : ℕ) + 12 * 6 ^ (2 : ℕ) + 6 : ℝ) ^
        (3 * tau0)) / Real.log 2
    norm_num only [show
      (6 ^ (4 : ℕ) + 12 * 6 ^ (2 : ℕ) + 6 : ℝ) = 1734 by norm_num]
    rw [show 3 * tau0 = rho0 by norm_num [tau0, rho0]]
    have h := rho_log_lower 1734 (1075988818 / 100000000) (1 / 100000000)
      (by norm_num) Numeric.log2_seventeen_thirty_four_mem
    norm_num at h ⊢
    exact h
  · simpa [classLogLower] using
      lower_log_of_lt Numeric.class5Lower (classValue 6 tau0 5)
        (1940474503 / 100000000) (1 / 10000000)
        (by norm_num [Numeric.class5Lower]) class5Lower_lt_classValue
        Numeric.log2_class5Lower_mem
  · simpa [classLogLower] using
      lower_log_of_lt Numeric.class6Lower (classValue 6 tau0 6)
        (636775151 / 25000000) (1 / 10000000)
        (by norm_num [Numeric.class6Lower]) class6Lower_lt_classValue
        Numeric.log2_class6Lower_mem
  · simpa [classLogLower] using
      lower_log_of_lt Numeric.class7Lower (classValue 6 tau0 7)
        (22633789 / 781250) (1 / 10000000)
        (by norm_num [Numeric.class7Lower]) class7Lower_lt_classValue
        Numeric.log2_class7Lower_mem
  · simpa [classLogLower] using
      lower_log_of_lt Numeric.class8Lower (classValue 6 tau0 8)
        (3007058303 / 100000000) (1 / 10000000)
        (by norm_num [Numeric.class8Lower]) class8Lower_lt_classValue
        Numeric.log2_class8Lower_mem
  · simpa [classLogLower] using
      lower_log_of_lt Numeric.class9Lower (classValue 6 tau0 9)
        (1565531661 / 50000000) (1 / 10000000)
        (by norm_num [Numeric.class9Lower]) class9Lower_lt_classValue
        Numeric.log2_class9Lower_mem

theorem marginalLog_le_upper (j : Fin 9) :
    Real.log (Numeric.numericMarginal j) / Real.log 2 ≤
      marginalLogUpper j := by
  have h := (abs_le.mp (Numeric.numericMarginal_log_mem j)).2
  unfold marginalLogUpper
  linarith

/-- The exact rational lower endpoint obtained by inserting all certified
coordinate intervals into the finite base-two logarithmic rate formula. -/
noncomputable def certifiedLog2Lower : ℝ :=
  (∑ i,
      (classMultiplicity i : ℝ) * (numericB i / 3) *
        classLogLower i) -
    ∑ j,
      Numeric.numericMarginal j * marginalLogUpper j

theorem certifiedLog2Lower_eq :
    certifiedLog2Lower =
      (881479201104670997653 / 73456554000000000000 : ℝ) := by
  unfold certifiedLog2Lower
  rw [numericB_explicit]
  norm_num [classLogLower, marginalLogUpper, classMultiplicity,
    Numeric.numericMarginal, Numeric.marginalLogCenter, rho0,
    Fin.sum_univ_succ]

theorem certifiedLog2Lower_gt :
    (12000001 / 1000000 : ℝ) < certifiedLog2Lower := by
  rw [certifiedLog2Lower_eq]
  norm_num

theorem numeric_globalRate_pos :
    0 < globalRate 6 tau0 numericB numericB := by
  rw [numeric_globalRate_eq]
  unfold numericCoreRate
  apply mul_pos
  · apply Finset.prod_pos
    intro i _hi
    exact pow_pos (Real.rpow_pos_of_pos (classValue_pos i) _) _
  · apply Finset.prod_pos
    intro j _hj
    rw [marginal_numericB_eq]
    exact Real.rpow_pos_of_pos (numericMarginal_pos j) _

/-- Exact expansion of Equation (5.3), specialized to the same rational
vector on both sides, as a finite base-two logarithmic sum. -/
theorem log2_numeric_globalRate_eq :
    Real.log (globalRate 6 tau0 numericB numericB) / Real.log 2 =
      (∑ i,
        (classMultiplicity i : ℝ) * (numericB i / 3) *
          (Real.log (classValue 6 tau0 i) / Real.log 2)) -
      ∑ j,
        Numeric.numericMarginal j *
          (Real.log (Numeric.numericMarginal j) / Real.log 2) := by
  have hclass (i : Fin 10) : 0 < classValue 6 tau0 i :=
    classValue_pos i
  have hmarg (j : Fin 9) : 0 < Numeric.numericMarginal j :=
    numericMarginal_pos j
  have hcomponent :
      0 < ∏ i,
        (Real.rpow (classValue 6 tau0 i) (numericB i / 3)) ^
          classMultiplicity i := by
    exact Finset.prod_pos fun i _ ↦
      pow_pos (Real.rpow_pos_of_pos (hclass i) _) _
  have hmarginal :
      0 < ∏ j,
        Real.rpow (marginal numericB j) (-marginal numericB j) := by
    exact Finset.prod_pos fun j _ ↦ by
      rw [marginal_numericB_eq]
      exact Real.rpow_pos_of_pos (hmarg j) _
  have hlogComponent :
      Real.log (∏ i,
        (Real.rpow (classValue 6 tau0 i) (numericB i / 3)) ^
          classMultiplicity i) =
        ∑ i, Real.log
          ((Real.rpow (classValue 6 tau0 i) (numericB i / 3)) ^
            classMultiplicity i) := by
    simpa using (Real.log_prod (s := Finset.univ) (fun i _ ↦
      (pow_pos (Real.rpow_pos_of_pos (hclass i) _) _).ne'))
  have hlogMarginal :
      Real.log (∏ j,
        Real.rpow (marginal numericB j) (-marginal numericB j)) =
        ∑ j, Real.log
          (Real.rpow (marginal numericB j) (-marginal numericB j)) := by
    simpa using (Real.log_prod (s := Finset.univ) (fun j _ ↦ by
      rw [marginal_numericB_eq]
      exact (Real.rpow_pos_of_pos (hmarg j) _).ne'))
  have hlogClassRpow (i : Fin 10) :
      Real.log (Real.rpow (classValue 6 tau0 i) (numericB i / 3)) =
        (numericB i / 3) * Real.log (classValue 6 tau0 i) :=
    Real.log_rpow (hclass i) _
  have hlogMarginalRpow (j : Fin 9) :
      Real.log
          (Real.rpow (Numeric.numericMarginal j)
            (-Numeric.numericMarginal j)) =
        (-Numeric.numericMarginal j) *
          Real.log (Numeric.numericMarginal j) :=
    Real.log_rpow (hmarg j) _
  rw [numeric_globalRate_eq]
  unfold numericCoreRate
  rw [Real.log_mul hcomponent.ne' hmarginal.ne']
  rw [hlogComponent]
  simp_rw [Real.log_pow]
  simp_rw [hlogClassRpow]
  rw [hlogMarginal]
  simp_rw [marginal_numericB_eq]
  simp_rw [hlogMarginalRpow]
  rw [add_div, Finset.sum_div, Finset.sum_div]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro i _hi <;> ring

/-- Certified finite-sum lower bound for the specialized global rate. -/
theorem certifiedLog2Lower_le_globalRate :
    certifiedLog2Lower ≤
      Real.log (globalRate 6 tau0 numericB numericB) / Real.log 2 := by
  rw [log2_numeric_globalRate_eq]
  unfold certifiedLog2Lower
  have hcomponent :
      (∑ i,
        (classMultiplicity i : ℝ) * (numericB i / 3) *
          classLogLower i) ≤
      ∑ i,
        (classMultiplicity i : ℝ) * (numericB i / 3) *
          (Real.log (classValue 6 tau0 i) / Real.log 2) := by
    apply Finset.sum_le_sum
    intro i _hi
    exact mul_le_mul_of_nonneg_left (classLogLower_le i)
      (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (numericB_pos i).le (by norm_num)))
  have hmarginal :
      (∑ j,
        Numeric.numericMarginal j *
          (Real.log (Numeric.numericMarginal j) / Real.log 2)) ≤
      ∑ j,
        Numeric.numericMarginal j * marginalLogUpper j := by
    apply Finset.sum_le_sum
    intro j _hj
    exact mul_le_mul_of_nonneg_left (marginalLog_le_upper j)
      (numericMarginal_pos j).le
  linarith

theorem log2_numeric_globalRate_gt :
    (12000001 / 1000000 : ℝ) <
      Real.log (globalRate 6 tau0 numericB numericB) / Real.log 2 :=
  certifiedLog2Lower_gt.trans_le certifiedLog2Lower_le_globalRate

theorem targetSquare_lt_two_rpow :
    (640000001 / 10000000 : ℝ) ^ (2 : ℕ) <
      (2 : ℝ) ^ (12000001 / 1000000 : ℝ) := by
  rw [show (12000001 / 1000000 : ℝ) =
      12 + 1 / 1000000 by norm_num,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp := Real.add_one_le_exp (Real.log 2 * (1 / 1000000 : ℝ))
  have hlog := Real.log_two_gt_d9
  nlinarith

/-- The exact fixed-profile scalar surplus needed before applying the outer
laser extraction theorem.  Its square root is strictly above `64.0000001`. -/
theorem targetSquare_lt_numeric_globalRate :
    (640000001 / 10000000 : ℝ) ^ (2 : ℕ) <
      globalRate 6 tau0 numericB numericB := by
  let G : ℝ := globalRate 6 tau0 numericB numericB
  have hG : 0 < G := by
    simpa only [G] using numeric_globalRate_pos
  have hlog :
      (12000001 / 1000000 : ℝ) < Real.log G / Real.log 2 := by
    simpa only [G] using log2_numeric_globalRate_gt
  have hmono :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlog
  calc
    (640000001 / 10000000 : ℝ) ^ (2 : ℕ) <
        (2 : ℝ) ^ (12000001 / 1000000 : ℝ) :=
      targetSquare_lt_two_rpow
    _ < (2 : ℝ) ^ (Real.log G / Real.log 2) := hmono
    _ = G := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hlog2ne : Real.log (2 : ℝ) ≠ 0 := scalar_log2_pos.ne'
      rw [show Real.log 2 * (Real.log G / Real.log 2) = Real.log G by
        field_simp]
      exact Real.exp_log hG

end MME.StothersFourth.NumericFinish

/-- The exact fixed-profile scalar surplus used by the Stothers fourth-power
specialization. Both the profile and the endpoint are rational; all
transcendental estimates above have explicit rational interval proofs. -/
theorem solution :
    let tau0 : ℝ := 23737 / 30000
    let numericB : Fin 10 → ℝ :=
      ![(98 : ℝ) / 97942072,
        (1862 : ℝ) / 97942072,
        (73075 : ℝ) / 97942072,
        (1023050 : ℝ) / 97942072,
        (3626000 : ℝ) / 97942072,
        (98000 : ℝ) / 97942072,
        (2156000 : ℝ) / 97942072,
        (13720000 : ℝ) / 97942072,
        (21560000 : ℝ) / 97942072,
        (38710000 : ℝ) / 97942072]
    (640000001 / 10000000 : ℝ) ^ (2 : ℕ) <
      MME.StothersFourth.globalRate 6 tau0 numericB numericB := by
  dsimp only
  simpa only [
      MME.StothersFourth.NumericFinish.tau0,
      MME.StothersFourth.NumericFinish.numericB_explicit] using
    MME.StothersFourth.NumericFinish.targetSquare_lt_numeric_globalRate
