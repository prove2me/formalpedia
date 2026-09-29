-- Prove2me | solution 1 for flt5_descent_explicit
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T13:56:30.018858+00:00
-- url     : https://prove2.me/submissions/d3883c59-0fec-4ef6-8976-f434619e36ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_flt5_z_zeta5_core

theorem solution (a b c w v c1 r s : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * w)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v)
    (hwv : w * v = c1 ^ 5) (hcop_wv : Int.gcd w v = 1) (hr : w = r ^ 5) (hs : v = s ^ 5) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  -- Helper: k|x, k|y → k | ↑(Int.gcd x y)
  have dvd_igcd : ∀ (k x y : ℤ), k ∣ x → k ∣ y → k ∣ ↑(Int.gcd x y) := by
    intro k x y hkx hky
    have hkx' : k.natAbs ∣ x.natAbs := Int.natAbs_dvd_natAbs.mpr hkx
    have hky' : k.natAbs ∣ y.natAbs := Int.natAbs_dvd_natAbs.mpr hky
    exact Int.natAbs_dvd.mp (by exact_mod_cast Nat.dvd_gcd hkx' hky')
  -- Step 1: gcd(r, s) = 1
  have hcop_rs : Int.gcd r s = 1 := by
    by_contra hne1
    obtain ⟨p, hp_prime, hp_dvd_gcd_rs⟩ := Nat.exists_prime_and_dvd hne1
    have hp_dvd_r : (p : ℤ) ∣ r :=
      dvd_trans (by exact_mod_cast hp_dvd_gcd_rs : (p : ℤ) ∣ ↑(Int.gcd r s))
                (Int.gcd_dvd_left r s)
    have hp_dvd_s : (p : ℤ) ∣ s :=
      dvd_trans (by exact_mod_cast hp_dvd_gcd_rs : (p : ℤ) ∣ ↑(Int.gcd r s))
                (Int.gcd_dvd_right r s)
    have hp_dvd_w : (p : ℤ) ∣ w := hr ▸ dvd_pow hp_dvd_r (by norm_num)
    have hp_dvd_v : (p : ℤ) ∣ v := hs ▸ dvd_pow hp_dvd_s (by norm_num)
    have h1 : (p : ℤ) ∣ ↑(Int.gcd w v) := dvd_igcd p w v hp_dvd_w hp_dvd_v
    rw [hcop_wv, Nat.cast_one] at h1
    have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have h2 : 2 ≤ (p : ℤ) := by exact_mod_cast hp_prime.two_le
    linarith
  -- Step 2: r * s = c1 (from (r*s)^5 = c1^5, odd power injective)
  have hrs : r * s = c1 := by
    have h5 : (r * s) ^ 5 = c1 ^ 5 := by rw [mul_pow, ← hr, ← hs]; exact hwv
    exact (Odd.strictMono_pow (by decide : Odd 5)).injective h5
  -- Step 3: delegate to ℤ[ζ_5] core
  have hw' : a + b = 5 ^ 4 * r ^ 5 := by rw [hw, hr]
  have hPhi' : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5 := by
    rw [hPhi, hs]
  exact flt5_z_zeta5_core a b c r s c1 h_eq h_cop h5c hc hc1 hw' hPhi' hcop_rs hrs
