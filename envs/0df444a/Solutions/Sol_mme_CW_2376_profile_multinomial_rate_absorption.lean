-- Prove2me | solution 1 for mme_CW_2376_profile_multinomial_rate_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:43:20.38444+00:00
-- url     : https://prove2.me/submissions/3ea015c6-f2d5-4ddd-a3cc-e88f85492289

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_mme_CW_2376_profile_induced_family

open MME Filter Real

set_option autoImplicit false

private theorem factorial_upper_coarse (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤
      6 * ((n + 1 : ℕ) : ℝ) * (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by
  let k := n - 1
  have hnk : n = k + 1 := by
    dsimp [k]
    omega
  rw [hnk]
  have hs : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 := by
    simpa [Function.comp_apply] using
      (Stirling.stirlingSeq'_antitone (Nat.zero_le k))
  have hs3 : Stirling.stirlingSeq (k + 1) ≤ 3 := by
    refine hs.trans ?_
    rw [Stirling.stirlingSeq_one]
    refine (_root_.div_le_self (Real.exp_pos 1).le ?_).trans Real.exp_one_lt_three.le
    rw [Real.one_le_sqrt]
    norm_num
  have hden :
      0 < Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
        (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
    positivity
  rw [Stirling.stirlingSeq] at hs3
  have hfac :
      (((k + 1).factorial : ℕ) : ℝ) ≤
        3 * (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) :=
    (div_le_iff₀ hden).mp hs3
  have hsqrt :
      Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) ≤
        2 * (((k + 1 + 1 : ℕ) : ℝ)) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · push_cast
      nlinarith [sq_nonneg (k : ℝ)]
  have hp : 0 ≤ (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
    positivity
  calc
    (((k + 1).factorial : ℕ) : ℝ)
        ≤ 3 * (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := hfac
    _ ≤ 3 * ((2 * (((k + 1 + 1 : ℕ) : ℝ))) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := by
      gcongr
    _ = 6 * (((k + 1 + 1 : ℕ) : ℝ)) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by ring

private theorem factorial_lower_coarse (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℕ) : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  apply le_trans ?_ (Stirling.le_factorial_stirling n)
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have hp : 0 ≤ (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by positivity
  exact le_mul_of_one_le_left hp hsqrt

private theorem marginal1 :
    2 * cw2376_a + 2 * cw2376_b + cw2376_c = (384072 : ℝ) / 3000000 := by
  norm_num [cw2376_a, cw2376_b, cw2376_c]

private theorem marginal2 :
    2 * cw2376_b + 2 * cw2376_d = (1308290 : ℝ) / 3000000 := by
  norm_num [cw2376_b, cw2376_d]

private theorem marginal3 :
    2 * cw2376_c + cw2376_d = (1231903 : ℝ) / 3000000 := by
  norm_num [cw2376_c, cw2376_d]

private theorem marginal4 :
    2 * cw2376_b = (75036 : ℝ) / 3000000 := by
  norm_num [cw2376_b]

private theorem marginal5 :
    cw2376_a = (699 : ℝ) / 3000000 := by
  norm_num [cw2376_a]

private theorem profileCountBase_pow_identity (m : ℕ) (hm : 1 ≤ m) :
    cw2376ProfileCountBase ^ (cw2376ProfileLength m) =
      (((cw2376ProfileLength m : ℕ) : ℝ) ^ cw2376ProfileLength m) /
        ((((384072 * m : ℕ) : ℝ) ^ (384072 * m)) *
          (((1308290 * m : ℕ) : ℝ) ^ (1308290 * m)) *
          (((1231903 * m : ℕ) : ℝ) ^ (1231903 * m)) *
          (((75036 * m : ℕ) : ℝ) ^ (75036 * m)) *
          (((699 * m : ℕ) : ℝ) ^ (699 * m))) := by
  have hH : 0 < cw2376ProfileCountBase := by
    unfold cw2376ProfileCountBase
    rw [marginal1, marginal2, marginal3, marginal4, marginal5]
    positivity
  have hN : 0 < ((cw2376ProfileLength m : ℕ) : ℝ) := by
    unfold cw2376ProfileLength
    positivity
  have ha : 0 < (((384072 * m : ℕ) : ℝ)) := by positivity
  have hb : 0 < (((1308290 * m : ℕ) : ℝ)) := by positivity
  have hc : 0 < (((1231903 * m : ℕ) : ℝ)) := by positivity
  have hd : 0 < (((75036 * m : ℕ) : ℝ)) := by positivity
  have he : 0 < (((699 * m : ℕ) : ℝ)) := by positivity
  apply Real.log_injOn_pos (pow_pos hH _) (div_pos (pow_pos hN _) (by positivity))
  unfold cw2376ProfileCountBase cw2376ProfileLength
  rw [marginal1, marginal2, marginal3, marginal4, marginal5]
  push_cast
  simp (disch := positivity) only [Real.log_pow, Real.log_div, Real.log_mul,
    Real.log_rpow, Real.log_one]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem five_div_powers
    (a b c d e N : ℕ) (hsum : a + b + c + d + e = N) :
    (((a : ℝ) / Real.exp 1) ^ a) *
        (((b : ℝ) / Real.exp 1) ^ b) *
        (((c : ℝ) / Real.exp 1) ^ c) *
        (((d : ℝ) / Real.exp 1) ^ d) *
        (((e : ℝ) / Real.exp 1) ^ e) =
      (((a : ℝ) ^ a) * ((b : ℝ) ^ b) * ((c : ℝ) ^ c) *
          ((d : ℝ) ^ d) * ((e : ℝ) ^ e)) /
        (Real.exp 1) ^ N := by
  simp only [div_pow]
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, div_mul_div_comm]
  congr 1
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, hsum]

private theorem profile_multinomial_entropy_bound (m : ℕ) (hm : 1 ≤ m) :
    cw2376ProfileCountBase ^ cw2376ProfileLength m ≤
      (6 : ℝ) ^ 5 * (((cw2376ProfileLength m + 1 : ℕ) : ℝ)) ^ 5 *
        ((cw2376ProfileLength m).factorial : ℝ) /
          (((384072 * m).factorial : ℝ) *
            ((1308290 * m).factorial : ℝ) *
            ((1231903 * m).factorial : ℝ) *
            ((75036 * m).factorial : ℝ) *
            ((699 * m).factorial : ℝ)) := by
  let N := cw2376ProfileLength m
  let a := 384072 * m
  let b := 1308290 * m
  let c := 1231903 * m
  let d := 75036 * m
  let e := 699 * m
  let E : ℝ := Real.exp 1
  let P : ℝ :=
    ((a : ℝ) ^ a) * ((b : ℝ) ^ b) * ((c : ℝ) ^ c) *
      ((d : ℝ) ^ d) * ((e : ℝ) ^ e)
  let R : ℝ :=
    (((a : ℝ) / E) ^ a) * (((b : ℝ) / E) ^ b) *
      (((c : ℝ) / E) ^ c) * (((d : ℝ) / E) ^ d) *
      (((e : ℝ) / E) ^ e)
  let Q : ℝ :=
    (a.factorial : ℝ) * (b.factorial : ℝ) * (c.factorial : ℝ) *
      (d.factorial : ℝ) * (e.factorial : ℝ)
  let D : ℝ := (6 : ℝ) ^ 5 * (((N + 1 : ℕ) : ℝ)) ^ 5
  have hsum : a + b + c + d + e = N := by
    dsimp [a, b, c, d, e, N, cw2376ProfileLength]
    omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hd : 1 ≤ d := by dsimp [d]; omega
  have he : 1 ≤ e := by dsimp [e]; omega
  have hN : 1 ≤ N := by dsimp [N, cw2376ProfileLength]; omega
  have haN : a + 1 ≤ N + 1 := by omega
  have hbN : b + 1 ≤ N + 1 := by omega
  have hcN : c + 1 ≤ N + 1 := by omega
  have hdN : d + 1 ≤ N + 1 := by omega
  have heN : e + 1 ≤ N + 1 := by omega
  have hQa := factorial_upper_coarse a ha
  have hQb := factorial_upper_coarse b hb
  have hQc := factorial_upper_coarse c hc
  have hQd := factorial_upper_coarse d hd
  have hQe := factorial_upper_coarse e he
  have hQ : Q ≤ D * R := by
    dsimp [Q, D, R, E]
    calc
      (a.factorial : ℝ) * (b.factorial : ℝ) * (c.factorial : ℝ) *
          (d.factorial : ℝ) * (e.factorial : ℝ)
          ≤ (6 * ((a + 1 : ℕ) : ℝ) * (((a : ℝ) / Real.exp 1) ^ a)) *
            (6 * ((b + 1 : ℕ) : ℝ) * (((b : ℝ) / Real.exp 1) ^ b)) *
            (6 * ((c + 1 : ℕ) : ℝ) * (((c : ℝ) / Real.exp 1) ^ c)) *
            (6 * ((d + 1 : ℕ) : ℝ) * (((d : ℝ) / Real.exp 1) ^ d)) *
            (6 * ((e + 1 : ℕ) : ℝ) * (((e : ℝ) / Real.exp 1) ^ e)) := by
              gcongr
      _ ≤ (6 * ((N + 1 : ℕ) : ℝ) * (((a : ℝ) / Real.exp 1) ^ a)) *
            (6 * ((N + 1 : ℕ) : ℝ) * (((b : ℝ) / Real.exp 1) ^ b)) *
            (6 * ((N + 1 : ℕ) : ℝ) * (((c : ℝ) / Real.exp 1) ^ c)) *
            (6 * ((N + 1 : ℕ) : ℝ) * (((d : ℝ) / Real.exp 1) ^ d)) *
            (6 * ((N + 1 : ℕ) : ℝ) * (((e : ℝ) / Real.exp 1) ^ e)) := by
              gcongr <;> exact_mod_cast ‹_›
      _ = (6 : ℝ) ^ 5 * (((N + 1 : ℕ) : ℝ)) ^ 5 *
            (((a : ℝ) / Real.exp 1) ^ a *
              ((b : ℝ) / Real.exp 1) ^ b *
              ((c : ℝ) / Real.exp 1) ^ c *
              ((d : ℝ) / Real.exp 1) ^ d *
              ((e : ℝ) / Real.exp 1) ^ e) := by ring
  have hR : R = P / E ^ N := by
    dsimp [R, P, E]
    exact five_div_powers a b c d e N hsum
  have hE : E ≠ 0 := by dsimp [E]; positivity
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hbase : cw2376ProfileCountBase ^ N = (N : ℝ) ^ N / P := by
    dsimp [N, P, a, b, c, d, e]
    exact profileCountBase_pow_identity m hm
  have hcancel : cw2376ProfileCountBase ^ N * R = ((N : ℝ) / E) ^ N := by
    rw [hbase, hR, div_pow]
    field_simp
  have hnum := factorial_lower_coarse N hN
  have hbase0 : 0 ≤ cw2376ProfileCountBase ^ N := by
    rw [hbase]
    positivity
  have hmain : cw2376ProfileCountBase ^ N * Q ≤ D * (N.factorial : ℝ) := by
    calc
      cw2376ProfileCountBase ^ N * Q
          ≤ cw2376ProfileCountBase ^ N * (D * R) := by gcongr
      _ = D * (cw2376ProfileCountBase ^ N * R) := by ring
      _ = D * (((N : ℝ) / E) ^ N) := by rw [hcancel]
      _ ≤ D * (N.factorial : ℝ) := by
        gcongr
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  change cw2376ProfileCountBase ^ N ≤ D * (N.factorial : ℝ) / Q at ⊢
  exact (le_div_iff₀ hQpos).2 hmain

private theorem profile_rate_exponent_dominates (m : ℕ)
    (hm : 16777217 ≤ m) :
    (100002 : ℝ) * Real.sqrt (((cw2376ProfileLength m + 1 : ℕ) : ℝ)) ≤
      (cw2376ProfileLength m : ℝ) * cw2376ProfileRate m := by
  have hm1 : 1 ≤ m := by omega
  have hmR : (16777217 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0R : (0 : ℝ) ≤ (m : ℝ) := by positivity
  let x : ℝ := Real.sqrt (((cw2376ProfileLength m + 1 : ℕ) : ℝ))
  let s : ℝ := Real.sqrt (Real.sqrt ((m : ℝ) + 1))
  have hx : x ≤ 1800 * Real.sqrt (m : ℝ) := by
    dsimp [x]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hm0R]
      unfold cw2376ProfileLength
      push_cast
      nlinarith
  have hs : s ≤ Real.sqrt (m : ℝ) / 64 := by
    dsimp [s]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [div_pow, Real.sq_sqrt hm0R]
      have hpoly :
          (0 : ℝ) ≤ ((m : ℝ) - 16777217) * ((m : ℝ) + 1) := by
        exact mul_nonneg (by linarith) (by positivity)
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · norm_num
        nlinarith
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hprod : x * s ≤ (225 / 8 : ℝ) * (m : ℝ) := by
    calc
      x * s ≤ (1800 * Real.sqrt (m : ℝ)) *
          (Real.sqrt (m : ℝ) / 64) := by gcongr
      _ = (225 / 8 : ℝ) * (m : ℝ) := by
        nlinarith [Real.sq_sqrt hm0R]
  change (100002 : ℝ) * x ≤
    ((cw2376ProfileLength m : ℕ) : ℝ) * s⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hspos).2
  unfold cw2376ProfileLength
  push_cast
  nlinarith

private theorem profile_polynomial_le_exp_two_sqrt (m : ℕ)
    (hm : 20000 ≤ m) :
    (6 : ℝ) ^ 5 * (((cw2376ProfileLength m + 1 : ℕ) : ℝ)) ^ 5 ≤
      Real.exp
        (2 * Real.sqrt (((cw2376ProfileLength m + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt (((cw2376ProfileLength m + 1 : ℕ) : ℝ))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x ^ 2 = (((cw2376ProfileLength m + 1 : ℕ) : ℝ)) := by
    dsimp [x]
    exact Real.sq_sqrt (by positivity)
  have h10 := Real.pow_div_factorial_le_exp x hx0 10
  have h2 := Real.pow_div_factorial_le_exp x hx0 2
  norm_num at h10 h2
  have hpoly :
      (((cw2376ProfileLength m + 1 : ℕ) : ℝ)) ^ 5 ≤
        3628800 * Real.exp x := by
    rw [← hx2, ← pow_mul]
    norm_num
    nlinarith [Real.exp_pos x]
  have hmR : (20000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hconst : (6 : ℝ) ^ 5 * 3628800 ≤ Real.exp x := by
    rw [show (6 : ℝ) ^ 5 * 3628800 = 28217548800 by norm_num]
    rw [hx2] at h2
    unfold cw2376ProfileLength at h2
    push_cast at h2
    nlinarith
  calc
    (6 : ℝ) ^ 5 * (((cw2376ProfileLength m + 1 : ℕ) : ℝ)) ^ 5
        ≤ (6 : ℝ) ^ 5 * (3628800 * Real.exp x) := by gcongr
    _ = ((6 : ℝ) ^ 5 * 3628800) * Real.exp x := by ring
    _ ≤ Real.exp x * Real.exp x := by gcongr
    _ = Real.exp (2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp
        (2 * Real.sqrt (((cw2376ProfileLength m + 1 : ℕ) : ℝ))) := by
      rfl

theorem solution :
    ∀ᶠ m : ℕ in atTop,
      let N := cw2376ProfileLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          (((384072 * m).factorial : ℝ) *
            ((1308290 * m).factorial : ℝ) *
            ((1231903 * m).factorial : ℝ) *
            ((75036 * m).factorial : ℝ) *
            ((699 * m).factorial : ℝ))
      (cw2376ProfileCountBase *
          Real.exp (-(cw2376ProfileRate m))) ^ N ≤
        V * Real.exp
          (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  rw [Filter.eventually_atTop]
  refine ⟨16777217, fun m hm => ?_⟩
  dsimp only
  let N := cw2376ProfileLength m
  let V : ℝ :=
    (N.factorial : ℝ) /
      (((384072 * m).factorial : ℝ) *
        ((1308290 * m).factorial : ℝ) *
        ((1231903 * m).factorial : ℝ) *
        ((75036 * m).factorial : ℝ) *
        ((699 * m).factorial : ℝ))
  let D : ℝ := (6 : ℝ) ^ 5 * (((N + 1 : ℕ) : ℝ)) ^ 5
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let r : ℝ := cw2376ProfileRate m
  have hm1 : 1 ≤ m := by omega
  have hm20 : 20000 ≤ m := by omega
  have hentropy : cw2376ProfileCountBase ^ N ≤ D * V := by
    dsimp [N, D, V]
    simpa only [mul_div_assoc] using
      (profile_multinomial_entropy_bound m hm1)
  have hpoly : D ≤ Real.exp (2 * x) := by
    dsimp [D, x, N]
    exact profile_polynomial_le_exp_two_sqrt m hm20
  have hdom : (100002 : ℝ) * x ≤ (N : ℝ) * r := by
    dsimp [x, N, r]
    exact profile_rate_exponent_dominates m hm
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hdecay : D * Real.exp (-((N : ℝ) * r)) ≤
      Real.exp (-100000 * x) := by
    calc
      D * Real.exp (-((N : ℝ) * r))
          ≤ Real.exp (2 * x) * Real.exp (-((N : ℝ) * r)) := by gcongr
      _ = Real.exp (2 * x - (N : ℝ) * r) := by
        rw [← Real.exp_add]
        congr 1
      _ ≤ Real.exp (-100000 * x) := by
        rw [Real.exp_le_exp]
        linarith
  change (cw2376ProfileCountBase * Real.exp (-r)) ^ N ≤
    V * Real.exp (-100000 * x)
  rw [mul_pow, ← Real.exp_nat_mul]
  calc
    cw2376ProfileCountBase ^ N * Real.exp ((N : ℝ) * -r)
        ≤ (D * V) * Real.exp ((N : ℝ) * -r) := by gcongr
    _ = V * (D * Real.exp (-((N : ℝ) * r))) := by ring
    _ ≤ V * Real.exp (-100000 * x) := by gcongr
