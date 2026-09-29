-- Prove2me | solution 1 for mme_CW_q6_primary_capacity_factorial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T01:17:43.12331+00:00
-- url     : https://prove2.me/submissions/cb1e2268-0976-4959-9d79-5971992df2ff

import Mathlib

set_option autoImplicit false

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

theorem solution
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
  rw [← hZ, ← hX, ← hB]
  field_simp
