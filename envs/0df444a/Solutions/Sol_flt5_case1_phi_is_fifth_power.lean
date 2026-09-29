-- Prove2me | solution 1 for flt5_case1_phi_is_fifth_power
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T09:11:35.366825+00:00
-- url     : https://prove2.me/submissions/ef39c18e-bbe3-4bb4-a337-fb5d910da4cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_coprime_fifth_power_factor
import Theorems.Thm_flt5_descent_gcd_one
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h_not5c : ¬(5 : ℤ) ∣ c) : ∃ e : ℤ, a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = e ^ 5 := by
  -- Phi10 * (a+b) = c^5 (reverse factor order)
  have hfact : (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) * (a + b) = c ^ 5 :=
    calc (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) * (a + b)
        = a ^ 5 + b ^ 5 := by ring
      _ = c ^ 5 := h_eq
  -- gcd(Phi10, a+b) = 1 (by symmetry from flt5_descent_gcd_one)
  have hgcd : Int.gcd (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) (a + b) = 1 := by
    have h := flt5_descent_gcd_one a b c h_eq h_cop h_not5c
    rwa [Int.gcd_comm] at h
  -- Apply coprime_fifth_power_factor to Phi10
  exact coprime_fifth_power_factor
    (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) (a + b) c hgcd hfact
