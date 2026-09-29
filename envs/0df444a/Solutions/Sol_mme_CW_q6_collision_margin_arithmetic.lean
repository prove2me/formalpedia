-- Prove2me | solution 1 for mme_CW_q6_collision_margin_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T01:16:05.775128+00:00
-- url     : https://prove2.me/submissions/c6583529-84b1-4549-af56-46340525d75c

import Mathlib

set_option autoImplicit false

/-- The 1/16 baseline, 1/8 concentration error, and 4/5 collision shares
fit strictly inside the available good-star mass. -/
theorem solution
    {B M X D R Q S Z : ℕ}
    (hXM : 4 * X ^ 2 ≤ M)
    (hRmargin : 16 * B * M ≤ R ^ 2)
    (hDmargin : 5 * B ≤ 8 * M * D)
    (hQ : 16 * M * Q ≤ S * Z) :
    M ^ 3 * D * R ^ 2 * Q +
          R ^ 2 * (2 * Z * B * X ^ 2 * S) +
          D * (2 * B * M ^ 3 * S * Z) ≤
        D * R ^ 2 * M ^ 2 * S * Z := by
  let A := M ^ 3 * D * R ^ 2 * Q
  let C := R ^ 2 * (2 * Z * B * X ^ 2 * S)
  let E := D * (2 * B * M ^ 3 * S * Z)
  let T := D * R ^ 2 * M ^ 2 * S * Z
  have hA16 : 16 * A ≤ T := by
    have h := Nat.mul_le_mul_left (D * R ^ 2 * M ^ 2) hQ
    simpa only [A, T] using (show
      16 * (M ^ 3 * D * R ^ 2 * Q) ≤
        D * R ^ 2 * M ^ 2 * S * Z by
          convert h using 1 <;> ring)
  have hE8 : 8 * E ≤ T := by
    have h := Nat.mul_le_mul_left (D * M ^ 2 * S * Z) hRmargin
    simpa only [E, T] using (show
      8 * (D * (2 * B * M ^ 3 * S * Z)) ≤
        D * R ^ 2 * M ^ 2 * S * Z by
          convert h using 1 <;> ring)
  have hBX₁ : 10 * B * X ^ 2 ≤ 16 * M * D * X ^ 2 := by
    have h := Nat.mul_le_mul_right (2 * X ^ 2) hDmargin
    convert h using 1 <;> ring
  have hBX₂ : 16 * M * D * X ^ 2 ≤ 4 * D * M ^ 2 := by
    have h := Nat.mul_le_mul_left (4 * D * M) hXM
    convert h using 1 <;> ring
  have hC5 : 5 * C ≤ 4 * T := by
    have h := Nat.mul_le_mul_left (R ^ 2 * S * Z) (hBX₁.trans hBX₂)
    simpa only [C, T] using (show
      5 * (R ^ 2 * (2 * Z * B * X ^ 2 * S)) ≤
        4 * (D * R ^ 2 * M ^ 2 * S * Z) by
          convert h using 1 <;> ring)
  have hA80 : 80 * A ≤ 5 * T := by
    have h := Nat.mul_le_mul_left 5 hA16
    convert h using 1 <;> ring
  have hC80 : 80 * C ≤ 64 * T := by
    have h := Nat.mul_le_mul_left 16 hC5
    convert h using 1 <;> ring
  have hE80 : 80 * E ≤ 10 * T := by
    have h := Nat.mul_le_mul_left 10 hE8
    convert h using 1 <;> ring
  have h79 : 80 * (A + C + E) ≤ 79 * T := by
    calc
      80 * (A + C + E) = 80 * A + 80 * C + 80 * E := by ring
      _ ≤ 5 * T + 64 * T + 10 * T :=
        Nat.add_le_add (Nat.add_le_add hA80 hC80) hE80
      _ = 79 * T := by ring
  have h80 : 80 * (A + C + E) ≤ 80 * T := by
    exact h79.trans (Nat.mul_le_mul_right T (by norm_num : 79 ≤ 80))
  have hfinal : A + C + E ≤ T :=
    Nat.le_of_mul_le_mul_left h80 (by norm_num : 0 < 80)
  simpa only [A, C, E, T] using hfinal
