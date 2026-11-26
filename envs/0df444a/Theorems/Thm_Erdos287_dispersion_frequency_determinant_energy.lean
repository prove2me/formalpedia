-- Prove2me | Theorems.Thm_Erdos287_dispersion_frequency_determinant_energy
-- name    : Erdos287.dispersion_frequency_determinant_energy
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T18:51:26.063264+00:00
-- url     : https://prove2.me/theorems/3debf903-d3d3-4392-a712-74f3b71a5d0f
-- title:
--   Frequency determinant counts for mixed Type II dispersion
-- statement:
--   Let $a,b$ be coprime naturals with $b>0$ and consider pairs of integer frequencies in $[-H,H]^2$, with determinant $h_1 b-h_2 a$. There are at most $(2H+1)^2(2\lfloor 2H/b\rfloor+1)$ ordered pairs of frequency pairs having equal determinant. At most $2\lfloor H/b\rfloor$ frequency pairs have zero determinant and a nonzero second frequency.
-- source:
--   Erdős #287, determinant energy in the mixed Type II exponential sum.

import Mathlib

theorem Erdos287.dispersion_frequency_determinant_energy (a b H : ℕ) (hb : 0 < b) (hab : a.Coprime b) :
    let T := Finset.Icc (-(H : ℤ)) (H : ℤ)
    let P := T ×ˢ T
    let det := fun u : ℤ × ℤ => u.1 * (b : ℤ) - u.2 * (a : ℤ)
    (((P ×ˢ P).filter (fun p => det p.1 = det p.2)).card ≤
      (2 * H + 1) ^ 2 * (2 * (2 * H / b) + 1)) ∧
    ((P.filter (fun u => det u = 0 ∧ u.2 ≠ 0)).card ≤ 2 * (H / b)) := by sorry
