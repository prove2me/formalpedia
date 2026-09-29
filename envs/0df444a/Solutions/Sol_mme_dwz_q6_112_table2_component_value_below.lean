-- Prove2me | solution 1 for mme_dwz_q6_112_table2_component_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T12:08:00.990529+00:00
-- url     : https://prove2.me/submissions/2c320bbd-3928-4ec5-b9f6-a109584110ec

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_q6_112_table2_primary_hash_family_rate
import Theorems.Thm_mme_dwz_q6_112_primary_hash_family_cyclic_value
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss

open Filter Topology
open MME MME.DWZSquare

set_option autoImplicit false

private noncomputable def b112 : ℝ := 21015 / 100000000

private noncomputable def countBase112 : ℝ :=
  4 / (Real.rpow (1 - 2 * b112) (1 - 2 * b112) *
    Real.rpow b112 (2 * b112))

theorem fixed_ideal_eq_countBase_pow (t : ℕ) (ht : 0 < t) :
    let N : ℕ := 50000000 * t
    let L : ℕ := 21015 * t
    let G : ℕ := 49978985 * t
    let ideal : ℝ :=
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
        ((((L : ℕ) : ℝ) ^ L) ^ 2 *
          (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
          (((N : ℕ) : ℝ) ^ N) ^ 4)
    ideal = countBase112 ^ (2 * N) := by
  dsimp only
  have hb : 0 < b112 := by norm_num [b112]
  have hp : 0 < 1 - 2 * b112 := by norm_num [b112]
  have hbase : 0 < countBase112 := by
    dsimp [countBase112]
    positivity
  have hN : 0 < 50000000 * t := by positivity
  have hL : 0 < 21015 * t := by positivity
  have hG : 0 < 49978985 * t := by positivity
  have hNR : 0 < ((50000000 * t : ℕ) : ℝ) := by exact_mod_cast hN
  have hLR : 0 < ((21015 * t : ℕ) : ℝ) := by exact_mod_cast hL
  have hGR : 0 < ((49978985 * t : ℕ) : ℝ) := by exact_mod_cast hG
  let lhs : ℝ :=
    ((((2 * (50000000 * t) : ℕ) : ℝ) ^
        (2 * (50000000 * t))) ^ 3) /
      (((((21015 * t : ℕ) : ℝ) ^ (21015 * t)) ^ 2) *
        (((2 * (49978985 * t) : ℕ) : ℝ) ^
          (2 * (49978985 * t))) *
        ((((50000000 * t : ℕ) : ℝ) ^ (50000000 * t)) ^ 4))
  let rhs : ℝ := countBase112 ^ (2 * (50000000 * t))
  change lhs = rhs
  have hlhs : 0 < lhs := by dsimp [lhs]; positivity
  have hrhs : 0 < rhs := by dsimp [rhs]; positivity
  apply Real.log_injOn_pos hlhs hrhs
  dsimp [lhs, rhs]
  push_cast
  simp (disch := positivity) only [Real.log_div, Real.log_mul,
    Real.log_pow]
  dsimp [countBase112]
  simp (disch := positivity) only [Real.log_div, Real.log_mul,
    Real.log_rpow]
  norm_num [b112]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlogp :
      Real.log (9995797 / 10000000 : ℝ) =
        Real.log 49978985 - Real.log 50000000 := by
    rw [show (9995797 / 10000000 : ℝ) =
      49978985 / 50000000 by norm_num]
    rw [Real.log_div (by norm_num) (by norm_num)]
  have hlogb :
      Real.log (4203 / 20000000 : ℝ) =
        Real.log 21015 - Real.log 100000000 := by
    rw [show (4203 / 20000000 : ℝ) =
      21015 / 100000000 by norm_num]
    rw [Real.log_div (by norm_num) (by norm_num)]
  have hlog100m :
      Real.log (100000000 : ℝ) =
        Real.log 2 + Real.log 50000000 := by
    rw [show (100000000 : ℝ) = 2 * 50000000 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog4, hlogp, hlogb, hlog100m]
  ring

theorem fixed_ideal_volume_eq_componentBase_cube_pow
    (tau : ℝ) (t : ℕ) (ht : 0 < t) :
    let N : ℕ := 50000000 * t
    let L : ℕ := 21015 * t
    let G : ℕ := 49978985 * t
    let ideal : ℝ :=
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
        ((((L : ℕ) : ℝ) ^ L) ^ 2 *
          (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
          (((N : ℕ) : ℝ) ^ N) ^ 4)
    let volume : ℝ :=
      ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau)
    ideal * volume =
      (componentBase tau (12 : Fin 15) ^ 3) ^ (2 * N) := by
  dsimp only
  rw [fixed_ideal_eq_countBase_pow t ht]
  have hb : 0 < b112 := by norm_num [b112]
  have hp : 0 < 1 - 2 * b112 := by norm_num [b112]
  have hcount : 0 < countBase112 := by
    dsimp [countBase112]
    positivity
  have hcomp :
      componentBase tau (12 : Fin 15) =
        Real.rpow countBase112 (1 / 3) *
          Real.rpow 6 ((2 - 2 * b112) * tau) := by
    simp [componentBase, countBase112, b112, splitB]
  rw [hcomp]
  have hN : 0 < 50000000 * t := by positivity
  have hNR : 0 < ((50000000 * t : ℕ) : ℝ) := by exact_mod_cast hN
  let lhs : ℝ :=
    countBase112 ^ (2 * (50000000 * t)) *
      ((((6 ^ (4 * (49978985 * t) + 2 * (21015 * t))) ^ 3 : ℕ) : ℝ) ^ tau)
  let rhs : ℝ :=
    ((Real.rpow countBase112 (1 / 3) *
      Real.rpow 6 ((2 - 2 * b112) * tau)) ^ 3) ^
        (2 * (50000000 * t))
  change lhs = rhs
  have hlhs : 0 < lhs := by dsimp [lhs]; positivity
  have hrhs : 0 < rhs := by dsimp [rhs]; positivity
  apply Real.log_injOn_pos hlhs hrhs
  dsimp [lhs, rhs]
  push_cast
  simp (disch := positivity) only [Real.log_mul, Real.log_pow,
    Real.log_rpow]
  norm_num [b112]
  ring

private noncomputable def polyC112 : ℝ :=
  32 * 6 ^ 7 * ((14 : ℕ).factorial : ℝ)

theorem q6_poly_le_exp_sqrt (N : ℕ) :
    32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7 ≤
      Real.exp (polyC112 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let C : ℝ := polyC112
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
    dsimp [x]
    exact Real.sq_sqrt (by positivity)
  have hx14 : x ^ 14 = (((N + 1 : ℕ) : ℝ)) ^ 7 := by
    calc
      x ^ 14 = (x ^ 2) ^ 7 := by norm_num [← pow_mul]
      _ = (((N + 1 : ℕ) : ℝ)) ^ 7 := by rw [hx2]
  have hC1 : (1 : ℝ) ≤ C := by
    dsimp [C, polyC112]
    norm_num
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC1
  have hCpow13 : (1 : ℝ) ≤ C ^ 13 := one_le_pow₀ hC1
  have hCpow : C ≤ C ^ 14 := by
    calc
      C = C * 1 := by ring
      _ ≤ C * C ^ 13 := by gcongr
      _ = C ^ 14 := by ring
  have hpoly :
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
          ((14 : ℕ).factorial : ℝ) ≤ (C * x) ^ 14 := by
    calc
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
            ((14 : ℕ).factorial : ℝ) = C * x ^ 14 := by
        rw [hx14]
        dsimp [C, polyC112]
        ring
      _ ≤ C ^ 14 * x ^ 14 := by gcongr
      _ = (C * x) ^ 14 := by ring
  calc
    32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7
        ≤ (C * x) ^ 14 / ((14 : ℕ).factorial : ℝ) := by
      apply (le_div_iff₀ (by positivity :
        (0 : ℝ) < ((14 : ℕ).factorial : ℝ))).2
      simpa only [mul_assoc] using hpoly
    _ ≤ Real.exp (C * x) :=
      Real.pow_div_factorial_le_exp (C * x) (mul_nonneg hC0 hx0) 14
    _ = Real.exp (polyC112 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
      rfl

private theorem factorial_upper_coarse_112 (n : ℕ) (hn : 1 ≤ n) :
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
    refine (_root_.div_le_self (Real.exp_pos 1).le ?_).trans
      Real.exp_one_lt_three.le
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

private theorem factorial_lower_coarse_112 (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℕ) : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  apply le_trans ?_ (Stirling.le_factorial_stirling n)
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have hp : 0 ≤ (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by positivity
  exact le_mul_of_one_le_left hp hsqrt

private theorem choose_two_stage_factorial_112
    (N L G : ℕ) (hLG : L + G = N) :
    (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        L.factorial ^ 2 * (2 * G).factorial =
      (2 * N).factorial := by
  have hL2N : L ≤ 2 * N := by omega
  have hLrem : L ≤ 2 * N - L := by omega
  have hfirst := Nat.choose_mul_factorial_mul_factorial hL2N
  have hsecond := Nat.choose_mul_factorial_mul_factorial hLrem
  have hrem : 2 * N - L - L = 2 * G := by omega
  rw [hrem] at hsecond
  calc
    (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          L.factorial ^ 2 * (2 * G).factorial =
        Nat.choose (2 * N) L * L.factorial *
          (Nat.choose (2 * N - L) L * L.factorial *
            (2 * G).factorial) := by ring
    _ = Nat.choose (2 * N) L * L.factorial *
          (2 * N - L).factorial := by rw [hsecond]
    _ = (2 * N).factorial := hfirst

private theorem choose_x_factorial_112
    (N L G : ℕ) (hLG : L + G = N) :
    Nat.choose N G * G.factorial * L.factorial = N.factorial := by
  have hG : G ≤ N := by omega
  simpa [show N - G = L by omega] using
    Nat.choose_mul_factorial_mul_factorial hG

private theorem choose_middle_factorial_112 (G : ℕ) :
    Nat.choose (2 * G) G * G.factorial ^ 2 = (2 * G).factorial := by
  have h :=
    Nat.choose_mul_factorial_mul_factorial (show G ≤ 2 * G by omega)
  rw [show 2 * G - G = G by omega] at h
  rw [pow_two]
  simpa only [mul_assoc] using h

private theorem capacity_factorial_identity_112
    (N L G : ℕ) (hLG : L + G = N) :
    let Z := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
    let X := Nat.choose N G
    let B := Nat.choose (2 * G) G
    (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
        (16 * (X : ℝ) ^ 4)) =
      (((2 * N).factorial : ℝ) ^ 3 /
        (16 * (L.factorial : ℝ) ^ 2 *
          ((2 * G).factorial : ℝ) * (N.factorial : ℝ) ^ 4)) := by
  dsimp only
  have hZ :
      ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
          (L.factorial : ℝ) ^ 2 * ((2 * G).factorial : ℝ) =
        ((2 * N).factorial : ℝ) := by
    exact_mod_cast choose_two_stage_factorial_112 N L G hLG
  have hX :
      (Nat.choose N G : ℝ) * (G.factorial : ℝ) * (L.factorial : ℝ) =
        (N.factorial : ℝ) := by
    exact_mod_cast choose_x_factorial_112 N L G hLG
  have hB :
      (Nat.choose (2 * G) G : ℝ) * (G.factorial : ℝ) ^ 2 =
        ((2 * G).factorial : ℝ) := by
    exact_mod_cast choose_middle_factorial_112 G
  have hLp : (0 : ℝ) < L.factorial := by positivity
  have hGp : (0 : ℝ) < G.factorial := by positivity
  have h2Gp : (0 : ℝ) < (2 * G).factorial := by positivity
  have hNp : (0 : ℝ) < N.factorial := by positivity
  have hXp : (0 : ℝ) < Nat.choose N G := by
    exact_mod_cast Nat.choose_pos (show G ≤ N by omega)
  rw [← hZ, ← hX, ← hB]
  field_simp

private theorem capacity_exp_factors_cancel_112
    (N L G : ℕ) (hLG : L + G = N) :
    ((((2 * N : ℕ) : ℝ) / Real.exp 1) ^ (2 * N)) ^ 3 /
        (((((L : ℕ) : ℝ) / Real.exp 1) ^ L) ^ 2 *
          ((((2 * G : ℕ) : ℝ) / Real.exp 1) ^ (2 * G)) *
          ((((N : ℕ) : ℝ) / Real.exp 1) ^ N) ^ 4) =
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
        ((((L : ℕ) : ℝ) ^ L) ^ 2 *
          (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
          (((N : ℕ) : ℝ) ^ N) ^ 4) := by
  have hsum : 2 * N * 3 = L * 2 + 2 * G + N * 4 := by omega
  simp only [div_pow, ← pow_mul]
  rw [hsum, pow_add, pow_add]
  field_simp
  have hexp :
      Real.exp 1 ^ (L * 2) * Real.exp 1 ^ (2 * G) *
          Real.exp 1 ^ (N * 4) =
        Real.exp 1 ^ (L * 2 + 2 * G + N * 4) := by
    rw [← pow_add, ← pow_add]
  calc
    ((2 * N : ℕ) : ℝ) ^ (L * 2) * ((2 * N : ℕ) : ℝ) ^ (2 * G) *
          Real.exp 1 ^ (L * 2) * Real.exp 1 ^ (2 * G) *
          Real.exp 1 ^ (N * 4) =
        (((2 * N : ℕ) : ℝ) ^ (L * 2) *
          ((2 * N : ℕ) : ℝ) ^ (2 * G)) *
          (Real.exp 1 ^ (L * 2) * Real.exp 1 ^ (2 * G) *
            Real.exp 1 ^ (N * 4)) := by ring
    _ = (((2 * N : ℕ) : ℝ) ^ (L * 2) *
          ((2 * N : ℕ) : ℝ) ^ (2 * G)) *
          Real.exp 1 ^ (L * 2 + 2 * G + N * 4) := by rw [hexp]
    _ = ((2 * N : ℕ) : ℝ) ^ (L * 2) *
          ((2 * N : ℕ) : ℝ) ^ (2 * G) *
          Real.exp 1 ^ (L * 2 + 2 * G + N * 4) := by ring

private theorem capacity_ideal_le_poly_mul_112
    (N L G : ℕ) (hL : 1 ≤ L) (hG : 1 ≤ G) (hLG : L + G = N) :
    let Z := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
    let X := Nat.choose N G
    let B := Nat.choose (2 * G) G
    let capacity : ℝ :=
      ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
    let ideal : ℝ :=
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
        ((((L : ℕ) : ℝ) ^ L) ^ 2 *
          (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
          (((N : ℕ) : ℝ) ^ N) ^ 4)
    ideal ≤
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) * capacity := by
  dsimp only
  rw [capacity_factorial_identity_112 N L G hLG]
  let E : ℝ := Real.exp 1
  let p2N : ℝ := (((2 * N : ℕ) : ℝ) / E) ^ (2 * N)
  let pL : ℝ := (((L : ℕ) : ℝ) / E) ^ L
  let p2G : ℝ := (((2 * G : ℕ) : ℝ) / E) ^ (2 * G)
  let pN : ℝ := (((N : ℕ) : ℝ) / E) ^ N
  let R : ℝ := pL ^ 2 * p2G * pN ^ 4
  let Q : ℝ :=
    16 * (L.factorial : ℝ) ^ 2 * ((2 * G).factorial : ℝ) *
      (N.factorial : ℝ) ^ 4
  let D : ℝ := 32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7
  have hN : 1 ≤ N := by omega
  have h2N : 1 ≤ 2 * N := by omega
  have h2G : 1 ≤ 2 * G := by omega
  have hLN : L + 1 ≤ N + 1 := by omega
  have hGN : 2 * G + 1 ≤ 2 * (N + 1) := by omega
  have hp2N := factorial_lower_coarse_112 (2 * N) h2N
  have hpL := factorial_upper_coarse_112 L hL
  have hp2G := factorial_upper_coarse_112 (2 * G) h2G
  have hpN := factorial_upper_coarse_112 N hN
  have hLcoef :
      (6 : ℝ) * (((L + 1 : ℕ) : ℝ)) ≤
        6 * (((N + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul_left 6 hLN
  have hGcoef :
      (6 : ℝ) * (((2 * G + 1 : ℕ) : ℝ)) ≤
        12 * (((N + 1 : ℕ) : ℝ)) := by
    have hGNR :
        (((2 * G + 1 : ℕ) : ℝ)) ≤
          2 * (((N + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hGN
    linarith
  have hLterm :
      6 * (((L + 1 : ℕ) : ℝ)) *
          (((L : ℕ) : ℝ) / Real.exp 1) ^ L ≤
        6 * (((N + 1 : ℕ) : ℝ)) *
          (((L : ℕ) : ℝ) / Real.exp 1) ^ L := by
    gcongr
  have hGterm :
      6 * (((2 * G + 1 : ℕ) : ℝ)) *
          (((2 * G : ℕ) : ℝ) / Real.exp 1) ^ (2 * G) ≤
        12 * (((N + 1 : ℕ) : ℝ)) *
          (((2 * G : ℕ) : ℝ) / Real.exp 1) ^ (2 * G) := by
    gcongr
  have hP : p2N ^ 3 ≤ (((2 * N).factorial : ℝ) ^ 3) := by
    dsimp [p2N, E]
    gcongr
  have hQ : Q ≤ D * R := by
    dsimp [Q, D, R, pL, p2G, pN, E]
    calc
      16 * (L.factorial : ℝ) ^ 2 * ((2 * G).factorial : ℝ) *
            (N.factorial : ℝ) ^ 4
          ≤ 16 *
              (6 * (((L + 1 : ℕ) : ℝ)) *
                (((L : ℕ) : ℝ) / Real.exp 1) ^ L) ^ 2 *
              (6 * ((((2 * G + 1 : ℕ) : ℝ))) *
                (((2 * G : ℕ) : ℝ) / Real.exp 1) ^ (2 * G)) *
              (6 * (((N + 1 : ℕ) : ℝ)) *
                (((N : ℕ) : ℝ) / Real.exp 1) ^ N) ^ 4 := by
            gcongr
      _ ≤ 16 *
              (6 * (((N + 1 : ℕ) : ℝ)) *
                (((L : ℕ) : ℝ) / Real.exp 1) ^ L) ^ 2 *
              (6 * ((((2 * G + 1 : ℕ) : ℝ))) *
                (((2 * G : ℕ) : ℝ) / Real.exp 1) ^ (2 * G)) *
              (6 * (((N + 1 : ℕ) : ℝ)) *
                (((N : ℕ) : ℝ) / Real.exp 1) ^ N) ^ 4 := by
            gcongr
      _ ≤ 16 *
              (6 * (((N + 1 : ℕ) : ℝ)) *
                (((L : ℕ) : ℝ) / Real.exp 1) ^ L) ^ 2 *
              (12 * (((N + 1 : ℕ) : ℝ)) *
                (((2 * G : ℕ) : ℝ) / Real.exp 1) ^ (2 * G)) *
              (6 * (((N + 1 : ℕ) : ℝ)) *
                (((N : ℕ) : ℝ) / Real.exp 1) ^ N) ^ 4 := by
            gcongr
      _ = (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
            (((((L : ℕ) : ℝ) / Real.exp 1) ^ L) ^ 2 *
              (((2 * G : ℕ) : ℝ) / Real.exp 1) ^ (2 * G) *
              ((((N : ℕ) : ℝ) / Real.exp 1) ^ N) ^ 4) := by ring
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hRpos : 0 < R := by
    dsimp [R, pL, p2G, pN, E]
    positivity
  have hideal :
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
          ((((L : ℕ) : ℝ) ^ L) ^ 2 *
            (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
            (((N : ℕ) : ℝ) ^ N) ^ 4) =
        p2N ^ 3 / R := by
    dsimp [p2N, R, pL, p2G, pN, E]
    exact (capacity_exp_factors_cancel_112 N L G hLG).symm
  rw [hideal]
  change p2N ^ 3 / R ≤ D *
    (((2 * N).factorial : ℝ) ^ 3 / Q)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hQpos).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hRpos).2
  calc
    p2N ^ 3 * Q ≤ p2N ^ 3 * (D * R) := by gcongr
    _ ≤ (((2 * N).factorial : ℝ) ^ 3) * (D * R) := by gcongr
    _ = D * ((2 * N).factorial : ℝ) ^ 3 * R := by ring

theorem fixed_capacity_sqrt_lower (t : ℕ) (ht : 0 < t) :
    let N : ℕ := 50000000 * t
    let L : ℕ := 21015 * t
    let G : ℕ := 49978985 * t
    let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
    let X : ℕ := Nat.choose N G
    let B : ℕ := Nat.choose (2 * G) G
    let capacity : ℝ :=
      ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
    let ideal : ℝ :=
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
        ((((L : ℕ) : ℝ) ^ L) ^ 2 *
          (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
          (((N : ℕ) : ℝ) ^ N) ^ 4)
    ideal * Real.exp
        (-polyC112 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤ capacity := by
  dsimp only
  let N : ℕ := 50000000 * t
  let L : ℕ := 21015 * t
  let G : ℕ := 49978985 * t
  let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let X : ℕ := Nat.choose N G
  let B : ℕ := Nat.choose (2 * G) G
  let capacity : ℝ :=
    ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
  let ideal : ℝ :=
    ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
      ((((L : ℕ) : ℝ) ^ L) ^ 2 *
        (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
        (((N : ℕ) : ℝ) ^ N) ^ 4)
  let D : ℝ := 32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7
  let E : ℝ :=
    Real.exp (polyC112 * Real.sqrt (((N + 1 : ℕ) : ℝ)))
  change ideal * Real.exp
    (-polyC112 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤ capacity
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hG : 1 ≤ G := by dsimp [G]; omega
  have hLG : L + G = N := by dsimp [L, G, N]; omega
  have hcap : ideal ≤ D * capacity := by
    simpa only [Z, X, B, capacity, ideal, D] using
      capacity_ideal_le_poly_mul_112 N L G hL hG hLG
  have hDE : D ≤ E := by
    simpa only [D, E] using q6_poly_le_exp_sqrt N
  have hcap0 : 0 ≤ capacity := by
    dsimp [capacity, Z, X, B]
    positivity
  have hIE : ideal ≤ E * capacity :=
    hcap.trans (mul_le_mul_of_nonneg_right hDE hcap0)
  have hEinv :
      Real.exp (-polyC112 * Real.sqrt (((N + 1 : ℕ) : ℝ))) = E⁻¹ := by
    dsimp [E]
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hEinv]
  rw [show E⁻¹ = 1 / E by ring]
  rw [mul_one_div]
  exact (div_le_iff₀ (by dsimp [E]; positivity)).2 (by
    simpa [mul_comm] using hIE)

theorem fixed_usable_rate_lower
    (tau C : ℝ) (t : ℕ) (ht : 0 < t) :
    let N : ℕ := 50000000 * t
    let L : ℕ := 21015 * t
    let G : ℕ := 49978985 * t
    let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
    let X : ℕ := Nat.choose N G
    let B : ℕ := Nat.choose (2 * G) G
    let capacity : ℝ :=
      ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
    let loss : ℝ :=
      Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ)))
    let volume : ℝ :=
      ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau)
    (componentBase tau (12 : Fin 15) ^ 3) ^ (2 * N) *
        Real.exp (-(polyC112 + 5 * C) *
          Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      capacity * loss ^ 5 * volume := by
  dsimp only
  let N : ℕ := 50000000 * t
  let L : ℕ := 21015 * t
  let G : ℕ := 49978985 * t
  let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let X : ℕ := Nat.choose N G
  let B : ℕ := Nat.choose (2 * G) G
  let capacity : ℝ :=
    ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
  let loss : ℝ :=
    Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ)))
  let volume : ℝ :=
    ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau)
  let ideal : ℝ :=
    ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
      ((((L : ℕ) : ℝ) ^ L) ^ 2 *
        (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
        (((N : ℕ) : ℝ) ^ N) ^ 4)
  let s : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  change (componentBase tau (12 : Fin 15) ^ 3) ^ (2 * N) *
      Real.exp (-(polyC112 + 5 * C) * s) ≤
    capacity * loss ^ 5 * volume
  have hcap : ideal * Real.exp (-polyC112 * s) ≤ capacity := by
    simpa only [N, L, G, Z, X, B, capacity, ideal, s] using
      fixed_capacity_sqrt_lower t ht
  have hid :
      ideal * volume =
        (componentBase tau (12 : Fin 15) ^ 3) ^ (2 * N) := by
    simpa only [N, L, G, ideal, volume] using
      fixed_ideal_volume_eq_componentBase_cube_pow tau t ht
  have hloss : loss ^ 5 = Real.exp (-5 * C * s) := by
    dsimp [loss]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hloss0 : 0 ≤ loss ^ 5 := by positivity
  have hvolume0 : 0 ≤ volume := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcap
    (mul_nonneg hloss0 hvolume0)
  have hexp :
      Real.exp (-(polyC112 + 5 * C) * s) =
        Real.exp (-polyC112 * s) * Real.exp (-5 * C * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (componentBase tau (12 : Fin 15) ^ 3) ^ (2 * N) *
          Real.exp (-(polyC112 + 5 * C) * s) =
        (ideal * Real.exp (-polyC112 * s)) * (loss ^ 5 * volume) := by
      rw [hloss, ← hid, hexp]
      ring
    _ ≤ capacity * (loss ^ 5 * volume) := hmul
    _ = capacity * loss ^ 5 * volume := by ring

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < componentBase tau (12 : Fin 15)) :
    HasSymmetricTauValueAtLeast (coupledObj K 6) tau V := by
  let base : ℝ := componentBase tau (12 : Fin 15)
  let B3 : ℝ := base ^ 3
  let V3 : ℝ := V ^ 3
  let M : ℝ := (V3 + B3) / 2
  have hbase : 0 < base := by
    dsimp [base]
    simp [componentBase, splitB]
    positivity
  have hB3 : 0 ≤ B3 := by
    dsimp [B3]
    positivity
  have hV3 : 0 ≤ V3 := by
    dsimp [V3]
    positivity
  have hV3B3 : V3 < B3 := by
    dsimp [V3, B3, base]
    exact pow_lt_pow_left₀ hVlt hV (by norm_num)
  have hV3M : V3 < M := by
    dsimp [M]
    linarith
  have hMB3 : M < B3 := by
    dsimp [M]
    linarith
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  obtain ⟨C, hC, hfamilies⟩ :=
    mme_dwz_q6_112_table2_primary_hash_family_rate
  let Ctot : ℝ := polyC112 + 5 * C
  have hpolyC : 0 ≤ polyC112 := by
    dsimp [polyC112]
    positivity
  have hCtot : 0 ≤ Ctot := by
    dsimp [Ctot]
    positivity
  have habsorb :=
    mme_strict_pow_absorbs_sqrt_exp_loss M B3 Ctot hM hMB3 hCtot
  have hscale :
      Tendsto (fun t : ℕ => 100000000 * t) atTop atTop := by
    simpa [nsmul_eq_mul, mul_comm] using
      ((tendsto_id : Tendsto (fun x : ℕ => x) atTop atTop).nsmul_atTop
        (by norm_num : 0 < (100000000 : ℕ)))
  have hpulled := hscale.eventually habsorb
  have hresult : ∀ᶠ t : ℕ in atTop,
      HasSymmetricTauValueAtLeast (coupledObj K 6) tau V := by
    filter_upwards [hfamilies, hpulled, eventually_gt_atTop 0]
      with t hfamily habs ht
    dsimp only at hfamily
    rcases hfamily with
      ⟨A, H, family, hHle, hAlower, hHlower, hcapacity⟩
    let N : ℕ := 50000000 * t
    let L : ℕ := 21015 * t
    let G : ℕ := 49978985 * t
    let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
    let X : ℕ := Nat.choose N G
    let middle : ℕ := Nat.choose (2 * G) G
    let capacity : ℝ :=
      ((Z : ℝ) ^ 3 * (middle : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
    let loss : ℝ :=
      Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ)))
    let volume : ℝ :=
      ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau)
    have hcapacity' : capacity * loss ^ 5 ≤ (A : ℝ) ^ 3 * (H : ℝ) ^ 2 := by
      simpa only [N, L, G, Z, X, middle, capacity, loss] using hcapacity
    have hrate :
        B3 ^ (2 * N) *
            Real.exp (-Ctot * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          capacity * loss ^ 5 * volume := by
      simpa only [B3, base, Ctot, N, L, G, Z, X, middle, capacity,
        loss, volume] using fixed_usable_rate_lower tau C t ht
    have hsqrt :
        Real.sqrt (((N + 1 : ℕ) : ℝ)) ≤
          Real.sqrt ((((2 * N) + 1 : ℕ) : ℝ)) := by
      apply Real.sqrt_le_sqrt
      push_cast
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith
    have hexp :
        Real.exp (-Ctot * Real.sqrt ((((2 * N) + 1 : ℕ) : ℝ))) ≤
          Real.exp (-Ctot * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have habs' :
        M ^ (2 * N) ≤
          B3 ^ (2 * N) *
            Real.exp (-Ctot * Real.sqrt ((((2 * N) + 1 : ℕ) : ℝ))) := by
      simpa only [N, show 100000000 * t = 2 * (50000000 * t) by omega]
        using habs
    have hMrate :
        M ^ (2 * N) ≤ capacity * loss ^ 5 * volume := by
      calc
        M ^ (2 * N) ≤
            B3 ^ (2 * N) *
              Real.exp (-Ctot * Real.sqrt ((((2 * N) + 1 : ℕ) : ℝ))) := habs'
        _ ≤ B3 ^ (2 * N) *
              Real.exp (-Ctot * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hexp (pow_nonneg hB3 _)
        _ ≤ capacity * loss ^ 5 * volume := hrate
    have hV3pow : V3 ^ (2 * N) < M ^ (2 * N) := by
      exact pow_lt_pow_left₀ hV3M hV3 (by omega)
    have hvolume : 0 ≤ volume := by
      dsimp [volume]
      positivity
    have hstrict :
        V3 ^ (2 * N) < (A : ℝ) ^ 3 * (H : ℝ) ^ 2 * volume := by
      calc
        V3 ^ (2 * N) < M ^ (2 * N) := hV3pow
        _ ≤ capacity * loss ^ 5 * volume := hMrate
        _ ≤ ((A : ℝ) ^ 3 * (H : ℝ) ^ 2) * volume := by
          exact mul_le_mul_of_nonneg_right hcapacity' hvolume
    have hpowered :
        HasTauValueAtLeast
          (cyclicSymmetrization ((coupledObj K 6).kronPow (2 * N)))
          tau (V3 ^ (2 * N)) := by
      apply mme_dwz_q6_112_primary_hash_family_cyclic_value
        tau htau N L G A H family (V3 ^ (2 * N)) (pow_nonneg hV3 _)
      simpa only [volume] using hstrict
    have hiso :=
      mme_cyclicSymmetrization_kronPow_isomorphic
        (coupledObj K 6) (2 * N)
    have hpow_of_cyclic :
        HasTauValueAtLeast
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N))
          tau (V3 ^ (2 * N)) :=
      mme_HasTauValueAtLeast_mono_restrict hiso.2 hpowered
    have hroot :
        HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V3 :=
      mme_HasTauValueAtLeast_kronPow_root
        (cyclicSymmetrization (coupledObj K 6)) tau V3 (2 * N)
        (by dsimp [N]; positivity) hV3 hpow_of_cyclic
    simpa only [HasSymmetricTauValueAtLeast, V3] using hroot
  exact hresult.exists.choose_spec
