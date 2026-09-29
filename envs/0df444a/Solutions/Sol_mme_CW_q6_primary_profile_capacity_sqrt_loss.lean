-- Prove2me | solution 1 for mme_CW_q6_primary_profile_capacity_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:44:04.182127+00:00
-- url     : https://prove2.me/submissions/4944fcdc-61e2-49d9-b9bc-29f407599ad6

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

open Filter Topology

set_option autoImplicit false

private theorem factorial_upper_coarse_q6 (n : ℕ) (hn : 1 ≤ n) :
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

private theorem factorial_lower_coarse_q6 (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℕ) : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  apply le_trans ?_ (Stirling.le_factorial_stirling n)
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have hp : 0 ≤ (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by positivity
  exact le_mul_of_one_le_left hp hsqrt

private theorem q6_choose_two_stage_factorial
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

private theorem q6_choose_x_factorial
    (N L G : ℕ) (hLG : L + G = N) :
    Nat.choose N G * G.factorial * L.factorial = N.factorial := by
  have hG : G ≤ N := by omega
  simpa [show N - G = L by omega] using
    Nat.choose_mul_factorial_mul_factorial hG

private theorem q6_choose_middle_factorial (G : ℕ) :
    Nat.choose (2 * G) G * G.factorial ^ 2 = (2 * G).factorial := by
  have h :=
    Nat.choose_mul_factorial_mul_factorial (show G ≤ 2 * G by omega)
  rw [show 2 * G - G = G by omega] at h
  rw [pow_two]
  simpa only [mul_assoc] using h

/-- Rewrite the finite q=6 capacity as one factorial quotient. -/
theorem q6_capacity_factorial_identity
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
    exact_mod_cast q6_choose_two_stage_factorial N L G hLG
  have hX :
      (Nat.choose N G : ℝ) * (G.factorial : ℝ) * (L.factorial : ℝ) =
        (N.factorial : ℝ) := by
    exact_mod_cast q6_choose_x_factorial N L G hLG
  have hB :
      (Nat.choose (2 * G) G : ℝ) * (G.factorial : ℝ) ^ 2 =
        ((2 * G).factorial : ℝ) := by
    exact_mod_cast q6_choose_middle_factorial G
  have hLp : (0 : ℝ) < L.factorial := by positivity
  have hGp : (0 : ℝ) < G.factorial := by positivity
  have h2Gp : (0 : ℝ) < (2 * G).factorial := by positivity
  have hNp : (0 : ℝ) < N.factorial := by positivity
  have hXp : (0 : ℝ) < Nat.choose N G := by
    exact_mod_cast Nat.choose_pos (show G ≤ N by omega)
  rw [← hZ, ← hX, ← hB]
  field_simp

private theorem q6_capacity_exp_factors_cancel
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

/-- A polynomial-loss lower bound for the finite q=6 multinomial capacity. -/
theorem q6_capacity_ideal_le_poly_mul
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
  rw [q6_capacity_factorial_identity N L G hLG]
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
  have hp2N := factorial_lower_coarse_q6 (2 * N) h2N
  have hpL := factorial_upper_coarse_q6 L hL
  have hp2G := factorial_upper_coarse_q6 (2 * G) h2G
  have hpN := factorial_upper_coarse_q6 N hN
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
    exact (q6_capacity_exp_factors_cancel N L G hLG).symm
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

/-- Algebraic form of the optimized q=6 profile ratio. -/
theorem q6_capacity_ideal_side_ratio_identity
    (N L G : ℕ) (hL : 0 < L) (hG : 0 < G) (hLG : L + G = N)
    (t : ℝ) (ht : 0 < t) :
    let ideal : ℝ :=
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
        ((((L : ℕ) : ℝ) ^ L) ^ 2 *
          (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
          (((N : ℕ) : ℝ) ^ N) ^ 4)
    let ratio : ℝ :=
      ((2 : ℝ) ^ L * t ^ G * (N : ℝ) ^ N) /
        ((L : ℝ) ^ L * (G : ℝ) ^ G * (t + 2) ^ N)
    ideal * t ^ (4 * G + 2 * L) =
      (4 * t * (t + 2)) ^ (2 * N) * ratio ^ 2 := by
  dsimp only
  have ht2 : 0 < t + 2 := by linarith
  have hN : 0 < N := by omega
  have hleft :
      0 < (((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
            ((((L : ℕ) : ℝ) ^ L) ^ 2 *
              (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
              (((N : ℕ) : ℝ) ^ N) ^ 4)) *
          t ^ (4 * G + 2 * L) := by positivity
  have hright :
      0 < (4 * t * (t + 2)) ^ (2 * N) *
          ((((2 : ℝ) ^ L * t ^ G * (N : ℝ) ^ N) /
            ((L : ℝ) ^ L * (G : ℝ) ^ G * (t + 2) ^ N)) ^ 2) := by
    positivity
  apply Real.log_injOn_pos hleft hright
  push_cast
  simp (disch := positivity) only [Real.log_mul, Real.log_div,
    Real.log_pow]
  push_cast
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hlog4]
  subst N
  norm_num
  ring

/-- Rounding the optimal profile down costs only a fixed factor. -/
theorem q6_floor_profile_ratio_lower
    (t : ℝ) (ht : 2 ≤ t) (N L G : ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hG : 0 < G) (hLG : L + G = N)
    (hfloorLe : (L : ℝ) ≤ (2 / (t + 2)) * (N : ℝ))
    (hfloorLt : (2 / (t + 2)) * (N : ℝ) < (L : ℝ) + 1) :
    Real.exp (-2) ≤
      ((((2 / (t + 2)) * (N : ℝ)) / (L : ℝ)) ^ L) *
        ((((t / (t + 2)) * (N : ℝ)) / (G : ℝ)) ^ G) := by
  let a : ℝ := 2 / (t + 2)
  let g : ℝ := t / (t + 2)
  let y : ℝ := g * (N : ℝ)
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have ht2pos : 0 < t + 2 := by linarith
  have hapos : 0 < a := by dsimp [a]; positivity
  have hgpos : 0 < g := by dsimp [g]; positivity
  have hag : a + g = 1 := by
    dsimp [a, g]
    field_simp
    ring
  have hgHalf : (1 / 2 : ℝ) ≤ g := by
    dsimp [g]
    apply (le_div_iff₀ ht2pos).2
    nlinarith
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hy1 : 1 ≤ y := by
    dsimp [y]
    nlinarith [mul_le_mul_of_nonneg_right hgHalf (by positivity : (0 : ℝ) ≤ N)]
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hLGR : (L : ℝ) + (G : ℝ) = (N : ℝ) := by exact_mod_cast hLG
  have hfloorLe' : (L : ℝ) ≤ a * (N : ℝ) := by
    simpa only [a] using hfloorLe
  have hfloorLt' : a * (N : ℝ) < (L : ℝ) + 1 := by
    simpa only [a] using hfloorLt
  have hyG : y ≤ (G : ℝ) := by
    dsimp [y]
    nlinarith
  have hGy : (G : ℝ) < y + 1 := by
    dsimp [y]
    nlinarith
  have hGposR : (0 : ℝ) < G := by exact_mod_cast hG
  have hLposR : (0 : ℝ) < L := by exact_mod_cast hL
  have hfirstBase : 1 ≤ (a * (N : ℝ)) / (L : ℝ) := by
    apply (le_div_iff₀ hLposR).2
    simpa only [one_mul] using hfloorLe'
  have hfirst : 1 ≤ ((a * (N : ℝ)) / (L : ℝ)) ^ L := by
    exact one_le_pow₀ hfirstBase
  have hGyPos : 0 < (G : ℝ) / y := div_pos hGposR hypos
  have hyDivGPos : 0 < y / (G : ℝ) := div_pos hypos hGposR
  have hdelta0 : 0 ≤ (G : ℝ) - y := sub_nonneg.2 hyG
  have hdelta1 : (G : ℝ) - y ≤ 1 := by linarith
  have hquotient : (G : ℝ) / y ≤ 2 := by
    apply (div_le_iff₀ hypos).2
    nlinarith
  have hrewrite :
      (G : ℝ) * ((G : ℝ) / y - 1) =
        ((G : ℝ) / y) * ((G : ℝ) - y) := by
    field_simp
  have hquad : (G : ℝ) * ((G : ℝ) / y - 1) ≤ 2 := by
    rw [hrewrite]
    calc
      (G : ℝ) / y * ((G : ℝ) - y) ≤
          2 * ((G : ℝ) - y) := by gcongr
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := by ring
  have hlogUpper :
      Real.log ((G : ℝ) / y) ≤ (G : ℝ) / y - 1 :=
    Real.log_le_sub_one_of_pos hGyPos
  have hGlog :
      (G : ℝ) * Real.log ((G : ℝ) / y) ≤ 2 := by
    calc
      (G : ℝ) * Real.log ((G : ℝ) / y) ≤
          (G : ℝ) * ((G : ℝ) / y - 1) := by gcongr
      _ ≤ 2 := hquad
  have hlogRecip :
      Real.log (y / (G : ℝ)) = -Real.log ((G : ℝ) / y) := by
    rw [Real.log_div hypos.ne' hGposR.ne',
      Real.log_div hGposR.ne' hypos.ne']
    ring
  have hsecondLog :
      (-2 : ℝ) ≤ Real.log ((y / (G : ℝ)) ^ G) := by
    rw [Real.log_pow, hlogRecip]
    push_cast
    linarith
  have hsecond :
      Real.exp (-2) ≤ (y / (G : ℝ)) ^ G :=
    (Real.le_log_iff_exp_le (pow_pos hyDivGPos G)).1 hsecondLog
  change Real.exp (-2) ≤
    ((a * (N : ℝ)) / (L : ℝ)) ^ L * (y / (G : ℝ)) ^ G
  exact hsecond.trans (le_mul_of_one_le_left (pow_nonneg hyDivGPos.le G) hfirst)

theorem q6_profile_ratio_eq_floor_product
    (t : ℝ) (ht : 0 < t) (N L G : ℕ)
    (hL : 0 < L) (hG : 0 < G) (hLG : L + G = N) :
    (((2 : ℝ) ^ L * t ^ G * (N : ℝ) ^ N) /
        ((L : ℝ) ^ L * (G : ℝ) ^ G * (t + 2) ^ N)) =
      ((((2 / (t + 2)) * (N : ℝ)) / (L : ℝ)) ^ L) *
        ((((t / (t + 2)) * (N : ℝ)) / (G : ℝ)) ^ G) := by
  have ht2 : 0 < t + 2 := by linarith
  have hN : 0 < N := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hleft :
      0 < (((2 : ℝ) ^ L * t ^ G * (N : ℝ) ^ N) /
        ((L : ℝ) ^ L * (G : ℝ) ^ G * (t + 2) ^ N)) := by
    positivity
  have hright :
      0 < ((((2 / (t + 2)) * (N : ℝ)) / (L : ℝ)) ^ L) *
        ((((t / (t + 2)) * (N : ℝ)) / (G : ℝ)) ^ G) := by
    positivity
  apply Real.log_injOn_pos hleft hright
  push_cast
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow]
  subst N
  simp only [Nat.cast_add]
  ring

theorem q6_capacity_ideal_side_optimized_lower
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (N L G : ℕ) (hN : 2 ≤ N) (hL : 0 < L) (hG : 0 < G)
    (hLG : L + G = N)
    (hfloorLe :
      (L : ℝ) ≤ (2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ))
    (hfloorLt :
      (2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ) < (L : ℝ) + 1) :
    let t : ℝ := (6 : ℝ) ^ (3 * tau)
    let raw : ℝ := 4 * t * (t + 2)
    let ideal : ℝ :=
      ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
        ((((L : ℕ) : ℝ) ^ L) ^ 2 *
          (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
          (((N : ℕ) : ℝ) ^ N) ^ 4)
    raw ^ (2 * N) * Real.exp (-4) ≤
      ideal * t ^ (4 * G + 2 * L) := by
  dsimp only
  let t : ℝ := (6 : ℝ) ^ (3 * tau)
  let ratio : ℝ :=
    ((2 : ℝ) ^ L * t ^ G * (N : ℝ) ^ N) /
      ((L : ℝ) ^ L * (G : ℝ) ^ G * (t + 2) ^ N)
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht36 : (36 : ℝ) ≤ t := by
    dsimp [t]
    calc
      (36 : ℝ) = (6 : ℝ) ^ (2 : ℕ) := by norm_num
      _ = (6 : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast 6 2).symm
      _ ≤ (6 : ℝ) ^ (3 * tau) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) htau
  have hprod := q6_floor_profile_ratio_lower t (by linarith) N L G
    hN hL hG hLG (by simpa only [t] using hfloorLe)
      (by simpa only [t] using hfloorLt)
  have hratio : Real.exp (-2) ≤ ratio := by
    dsimp [ratio]
    rw [q6_profile_ratio_eq_floor_product t htpos N L G hL hG hLG]
    exact hprod
  have hsq : Real.exp (-4) ≤ ratio ^ 2 := by
    rw [show Real.exp (-4) = Real.exp (-2) ^ 2 by
      calc
        Real.exp (-4) = Real.exp ((-2) + (-2)) := by norm_num
        _ = Real.exp (-2) * Real.exp (-2) := Real.exp_add _ _
        _ = Real.exp (-2) ^ 2 := by ring]
    gcongr
  rw [q6_capacity_ideal_side_ratio_identity N L G hL hG hLG t htpos]
  dsimp only [ratio] at hsq ⊢
  gcongr

theorem q6_side_tau_identity (tau : ℝ) (L G : ℕ) :
    let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
    ((((side * side * side : ℕ) : ℝ)) ^ tau) =
      (((6 : ℝ) ^ (3 * tau)) ^ (4 * G + 2 * L)) := by
  dsimp only
  have hleft :
      0 < ((((36 ^ (2 * G) * 6 ^ (2 * L)) *
          (36 ^ (2 * G) * 6 ^ (2 * L)) *
          (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau := by
    positivity
  have hright :
      0 < (((6 : ℝ) ^ (3 * tau)) ^ (4 * G + 2 * L)) := by
    positivity
  apply Real.log_injOn_pos hleft hright
  push_cast
  simp (disch := positivity) only [Real.log_rpow, Real.log_mul, Real.log_pow]
  have hlog36 : Real.log (36 : ℝ) = 2 * Real.log 6 := by
    rw [show (36 : ℝ) = 6 * 6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hlog36]
  push_cast
  ring

theorem q6_capacity_polynomial_absorbed :
    ∀ᶠ N : ℕ in atTop,
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7 ≤
        Real.exp (((N : ℕ) : ℝ) * loss / 2 - 4) := by
  let C : ℕ := 32 * 6 ^ 7 * 81 * (16 : ℕ).factorial * 4 ^ 16
  rw [Filter.eventually_atTop]
  refine ⟨max 2 C, fun N hN => ?_⟩
  dsimp only
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let s : ℝ := Real.sqrt r
  let x : ℝ := (N : ℝ) * s⁻¹ / 2
  have hN2 : 2 ≤ N := le_trans (le_max_left 2 C) hN
  have hCN : C ≤ N := le_trans (le_max_right 2 C) hN
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hspos : 0 < s := by dsimp [s]; positivity
  have hr1 : 1 ≤ r := by
    dsimp [r]
    rw [Real.one_le_sqrt]
    push_cast
    linarith
  have hsle : s ≤ r := by
    dsimp [s]
    rw [Real.sqrt_le_iff]
    constructor
    · exact hrpos.le
    · nlinarith
  have hr2 : r ^ 2 = ((N + 1 : ℕ) : ℝ) := by
    dsimp [r]
    exact Real.sq_sqrt (by positivity)
  have hrs : r * s ≤ r * r := by gcongr
  have hrsN : r * s ≤ (((N + 1 : ℕ) : ℝ)) := by
    nlinarith [hr2]
  have hN1 : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    push_cast
    linarith
  have hxlower : r / 4 ≤ x := by
    dsimp [x]
    rw [show (s : ℝ)⁻¹ = 1 / s by ring]
    field_simp
    nlinarith [hrsN, hN1]
  have hxnonneg : 0 ≤ x := by dsimp [x]; positivity
  have hpowLower : (r / 4) ^ 16 ≤ x ^ 16 := by gcongr
  have hrpow : (r / 4) ^ 16 =
      (((N + 1 : ℕ) : ℝ)) ^ 8 / (4 : ℝ) ^ 16 := by
    rw [div_pow]
    congr 1
    calc
      r ^ 16 = (r ^ 2) ^ 8 := by norm_num [← pow_mul]
      _ = (((N + 1 : ℕ) : ℝ)) ^ 8 := by rw [hr2]
  have hexp4 : Real.exp 4 ≤ 81 := by
    calc
      Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [show (4 : ℝ) = 1 + 1 + 1 + 1 by norm_num,
          Real.exp_add, Real.exp_add, Real.exp_add]
        ring
      _ ≤ (3 : ℝ) ^ 4 := by gcongr; exact Real.exp_one_lt_three.le
      _ = 81 := by norm_num
  have hconstR :
      (32 : ℝ) * 6 ^ 7 * 81 * ((16 : ℕ).factorial : ℝ) * 4 ^ 16 ≤
        (N : ℝ) := by
    exact_mod_cast hCN
  have hpolyPower :
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
          Real.exp 4 * ((16 : ℕ).factorial : ℝ) * 4 ^ 16 ≤
        (((N + 1 : ℕ) : ℝ)) ^ 8 := by
    calc
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
            Real.exp 4 * ((16 : ℕ).factorial : ℝ) * 4 ^ 16
          ≤ (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
            81 * ((16 : ℕ).factorial : ℝ) * 4 ^ 16 := by gcongr
      _ = ((32 : ℝ) * 6 ^ 7 * 81 * ((16 : ℕ).factorial : ℝ) * 4 ^ 16) *
          (((N + 1 : ℕ) : ℝ)) ^ 7 := by ring
      _ ≤ (N : ℝ) * (((N + 1 : ℕ) : ℝ)) ^ 7 := by gcongr
      _ ≤ (((N + 1 : ℕ) : ℝ)) * (((N + 1 : ℕ) : ℝ)) ^ 7 := by
        gcongr
        push_cast
        linarith
      _ = (((N + 1 : ℕ) : ℝ)) ^ 8 := by ring
  have hpolyX :
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
          Real.exp 4 * ((16 : ℕ).factorial : ℝ) ≤ x ^ 16 := by
    have hmul :
        ((32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
            Real.exp 4 * ((16 : ℕ).factorial : ℝ)) * 4 ^ 16 ≤
          x ^ 16 * 4 ^ 16 := by
      calc
      ((32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
            Real.exp 4 * ((16 : ℕ).factorial : ℝ)) * 4 ^ 16
          ≤ (((N + 1 : ℕ) : ℝ)) ^ 8 := by
            simpa only [mul_assoc] using hpolyPower
      _ = (r / 4) ^ 16 * 4 ^ 16 := by rw [hrpow]; field_simp
      _ ≤ x ^ 16 * 4 ^ 16 := by gcongr
    exact le_of_mul_le_mul_right hmul (by positivity : (0 : ℝ) < 4 ^ 16)
  have hpowExp := Real.pow_div_factorial_le_exp x hxnonneg 16
  have hpolyExp :
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) *
          Real.exp 4 ≤ Real.exp x := by
    calc
      (32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7) * Real.exp 4
          ≤ x ^ 16 / ((16 : ℕ).factorial : ℝ) := by
            apply (le_div_iff₀ (by positivity : (0 : ℝ) < (16 : ℕ).factorial)).2
            simpa only [mul_assoc] using hpolyX
      _ ≤ Real.exp x := hpowExp
  have hxLoss :
      x = ((N : ℕ) : ℝ) *
          (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹ / 2 := by
    rfl
  rw [← hxLoss]
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos 4)).2
  exact hpolyExp

theorem q6_quarter_root_scratch_solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let capacity : ℝ :=
        ((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
          (16 * (Xcount : ℝ) ^ 4)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
        (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
          (capacity * Real.exp (-((N : ℝ) * loss / 2))) *
            ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  filter_upwards [q6_capacity_polynomial_absorbed,
    (Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩)] with N hpoly hN2
  dsimp only at hpoly ⊢
  let t : ℝ := (6 : ℝ) ^ (3 * tau)
  let L : ℕ := ⌊(2 / (t + 2)) * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let raw : ℝ := 4 * t * (t + 2)
  let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let X : ℕ := Nat.choose N G
  let B : ℕ := Nat.choose (2 * G) G
  let capacity : ℝ := ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
    (16 * (X : ℝ) ^ 4)
  let loss : ℝ :=
    (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
  let D : ℝ := 32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7
  let ideal : ℝ :=
    ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
      ((((L : ℕ) : ℝ) ^ L) ^ 2 *
        (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
        (((N : ℕ) : ℝ) ^ N) ^ 4)
  let sideTau : ℝ := ((((side * side * side : ℕ) : ℝ)) ^ tau)
  let xloss : ℝ := (N : ℝ) * loss / 2
  change (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
    (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
      (capacity * Real.exp (-xloss)) * sideTau
  change D ≤ Real.exp (xloss - 4) at hpoly
  rintro ⟨hL, hLG, hratioCond⟩
  have hG : 0 < G := by omega
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht2pos : 0 < t + 2 := by positivity
  have hlambdaNonneg : 0 ≤ (2 / (t + 2)) * (N : ℝ) := by positivity
  have hfloorLe :
      (L : ℝ) ≤ (2 / (t + 2)) * (N : ℝ) := by
    dsimp [L]
    exact Nat.floor_le hlambdaNonneg
  have hfloorLt :
      (2 / (t + 2)) * (N : ℝ) < (L : ℝ) + 1 := by
    dsimp [L]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((2 / (t + 2)) * (N : ℝ))
  have hcapacity : ideal ≤ D * capacity := by
    simpa only [Z, X, B, capacity, ideal, D] using
      q6_capacity_ideal_le_poly_mul N L G
        (Nat.succ_le_iff.mpr hL) (Nat.succ_le_iff.mpr hG) hLG
  have hoptimized :
      raw ^ (2 * N) * Real.exp (-4) ≤
        ideal * t ^ (4 * G + 2 * L) := by
    simpa only [t, raw, ideal] using
      q6_capacity_ideal_side_optimized_lower tau htau N L G hN2 hL hG hLG
        (by simpa only [t] using hfloorLe)
        (by simpa only [t] using hfloorLt)
  have hside : sideTau = t ^ (4 * G + 2 * L) := by
    simpa only [sideTau, side, t] using q6_side_tau_identity tau L G
  have hoptimized' :
      raw ^ (2 * N) * Real.exp (-4) ≤ ideal * sideTau := by
    rwa [hside]
  have hchain :
      raw ^ (2 * N) * Real.exp (-4) ≤
        Real.exp (xloss - 4) * capacity * sideTau := by
    calc
      raw ^ (2 * N) * Real.exp (-4) ≤ ideal * sideTau := hoptimized'
      _ ≤ (D * capacity) * sideTau := by gcongr
      _ ≤ (Real.exp (xloss - 4) * capacity) * sideTau := by gcongr
      _ = Real.exp (xloss - 4) * capacity * sideTau := by ring
  have hsuff :
      raw ^ (2 * N) * Real.exp (-xloss) ≤ capacity * sideTau := by
    calc
      raw ^ (2 * N) * Real.exp (-xloss) =
          (raw ^ (2 * N) * Real.exp (-4)) /
            Real.exp (xloss - 4) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        calc
          raw ^ (2 * N) * Real.exp (-xloss) =
              raw ^ (2 * N) *
                (Real.exp (-4) * Real.exp (-(xloss - 4))) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring
          _ = raw ^ (2 * N) * Real.exp (-4) *
                Real.exp (-(xloss - 4)) := by ring
      _ ≤ capacity * sideTau := by
        apply (div_le_iff₀ (Real.exp_pos (xloss - 4))).2
        exact hchain.trans (le_of_eq (by ring))
  have hexpNeg : 0 ≤ Real.exp (-xloss) := (Real.exp_pos _).le
  calc
    (raw * Real.exp (-(loss / 2))) ^ (2 * N) =
        (raw ^ (2 * N) * Real.exp (-xloss)) *
          Real.exp (-xloss) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      calc
        raw ^ (2 * N) * Real.exp (((2 * N : ℕ) : ℝ) * (-(loss / 2))) =
            raw ^ (2 * N) * Real.exp (-xloss + -xloss) := by
          congr 2
          dsimp [xloss]
          push_cast
          ring
        _ = raw ^ (2 * N) *
              (Real.exp (-xloss) * Real.exp (-xloss)) := by
          rw [Real.exp_add]
        _ = (raw ^ (2 * N) * Real.exp (-xloss)) *
              Real.exp (-xloss) := by ring
    _ ≤ (capacity * sideTau) * Real.exp (-xloss) := by gcongr
    _ = (capacity * Real.exp (-xloss)) * sideTau := by ring

private noncomputable def q6PolyC : ℝ :=
  32 * 6 ^ 7 * ((14 : ℕ).factorial : ℝ)

private theorem q6_poly_le_exp_sqrt (N : ℕ) :
    32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7 ≤
      Real.exp (q6PolyC * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let C : ℝ := q6PolyC
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
    dsimp [x]
    exact Real.sq_sqrt (by positivity)
  have hx14 : x ^ 14 = (((N + 1 : ℕ) : ℝ)) ^ 7 := by
    calc
      x ^ 14 = (x ^ 2) ^ 7 := by norm_num [← pow_mul]
      _ = (((N + 1 : ℕ) : ℝ)) ^ 7 := by rw [hx2]
  have hC1 : (1 : ℝ) ≤ C := by
    dsimp [C, q6PolyC]
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
        dsimp [C, q6PolyC]
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
    _ = Real.exp (q6PolyC * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
      rfl

theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N L G : ℕ), 2 ≤ N → 0 < L → 0 < G → L + G = N →
        (L : ℝ) ≤
            (2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ) →
        (2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ) <
            (L : ℝ) + 1 →
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        let Z : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let X : ℕ := Nat.choose N G
        let B : ℕ := Nat.choose (2 * G) G
        let capacity : ℝ :=
          ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
        raw ^ (2 * N) *
            Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          capacity * ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  refine ⟨q6PolyC + 4, ?_, ?_⟩
  · dsimp [q6PolyC]
    positivity
  intro N L G hN hL hG hLG hfloorLe hfloorLt
  dsimp only
  let t : ℝ := (6 : ℝ) ^ (3 * tau)
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let raw : ℝ := 4 * t * (t + 2)
  let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let X : ℕ := Nat.choose N G
  let B : ℕ := Nat.choose (2 * G) G
  let capacity : ℝ := ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
    (16 * (X : ℝ) ^ 4)
  let D : ℝ := 32 * (6 : ℝ) ^ 7 * (((N + 1 : ℕ) : ℝ)) ^ 7
  let ideal : ℝ :=
    ((((2 * N : ℕ) : ℝ) ^ (2 * N)) ^ 3) /
      ((((L : ℕ) : ℝ) ^ L) ^ 2 *
        (((2 * G : ℕ) : ℝ) ^ (2 * G)) *
        (((N : ℕ) : ℝ) ^ N) ^ 4)
  let sideTau : ℝ := ((((side * side * side : ℕ) : ℝ)) ^ tau)
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  change raw ^ (2 * N) * Real.exp (-(q6PolyC + 4) * x) ≤
    capacity * sideTau
  have hx1 : 1 ≤ x := by
    dsimp [x]
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ N + 1 by omega)
  have hcapacity : ideal ≤ D * capacity := by
    simpa only [Z, X, B, capacity, ideal, D] using
      q6_capacity_ideal_le_poly_mul N L G
        (Nat.succ_le_iff.mpr hL) (Nat.succ_le_iff.mpr hG) hLG
  have hoptimized :
      raw ^ (2 * N) * Real.exp (-4) ≤
        ideal * t ^ (4 * G + 2 * L) := by
    simpa only [t, raw, ideal] using
      q6_capacity_ideal_side_optimized_lower tau htau N L G hN hL hG hLG
        (by simpa only [t] using hfloorLe)
        (by simpa only [t] using hfloorLt)
  have hside : sideTau = t ^ (4 * G + 2 * L) := by
    simpa only [sideTau, side, t] using q6_side_tau_identity tau L G
  have hDexp : D ≤ Real.exp (q6PolyC * x) := by
    simpa only [D, x] using q6_poly_le_exp_sqrt N
  have hDcancel : D * Real.exp (-(q6PolyC * x)) ≤ 1 := by
    calc
      D * Real.exp (-(q6PolyC * x)) ≤
          Real.exp (q6PolyC * x) * Real.exp (-(q6PolyC * x)) := by
        gcongr
      _ = 1 := by
        rw [← Real.exp_add]
        simp
  have htargetExp :
      Real.exp (-(q6PolyC + 4) * x) ≤
        Real.exp (-4) * Real.exp (-(q6PolyC * x)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hfour : (4 : ℝ) ≤ 4 * x := by nlinarith
    nlinarith
  calc
    raw ^ (2 * N) * Real.exp (-(q6PolyC + 4) * x)
        ≤ raw ^ (2 * N) *
            (Real.exp (-4) * Real.exp (-(q6PolyC * x))) := by
          gcongr
    _ = (raw ^ (2 * N) * Real.exp (-4)) *
          Real.exp (-(q6PolyC * x)) := by ring
    _ ≤ (ideal * t ^ (4 * G + 2 * L)) *
          Real.exp (-(q6PolyC * x)) := by gcongr
    _ = (ideal * Real.exp (-(q6PolyC * x))) *
          t ^ (4 * G + 2 * L) := by ring
    _ ≤ ((D * capacity) * Real.exp (-(q6PolyC * x))) *
          t ^ (4 * G + 2 * L) := by gcongr
    _ = (D * Real.exp (-(q6PolyC * x))) * capacity *
          t ^ (4 * G + 2 * L) := by ring
    _ ≤ 1 * capacity * t ^ (4 * G + 2 * L) := by gcongr
    _ = capacity * sideTau := by rw [hside]; ring
