-- Prove2me | solution 1 for flt5_coprime_wv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T13:16:55.348655+00:00
-- url     : https://prove2.me/submissions/9e09ec8c-793a-4f4e-8a57-8e1669780981

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution (a b c w v c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * w)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v)
    (hwv : w * v = c1 ^ 5) : Int.gcd w v = 1 := by
  haveI hfact5 : Fact (Nat.Prime 5) := ⟨by decide⟩
  -- Euclid's lemma for 5 via ZMod 5
  have euclid5 : ∀ x y : ℤ, (5 : ℤ) ∣ x * y → ¬(5 : ℤ) ∣ y → (5 : ℤ) ∣ x := by
    intro x y hxy hny
    have mul0 : ∀ a b : ZMod 5, a * b = 0 → b ≠ 0 → a = 0 := by decide
    have hxy0 : (x : ZMod 5) * (y : ZMod 5) = 0 := by
      have h : ((x * y : ℤ) : ZMod 5) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hxy
      push_cast at h; exact h
    have hy0 : (y : ZMod 5) ≠ 0 := by
      intro h; rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h; exact hny (by exact_mod_cast h)
    have hx0 := mul0 _ _ hxy0 hy0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0; exact_mod_cast hx0
  -- helper: k|x → k|y → k|gcd(x,y) (as ℤ)
  have dvd_igcd : ∀ (k x y : ℤ), k ∣ x → k ∣ y → k ∣ ↑(Int.gcd x y) := by
    intro k x y hkx hky
    have hkx' : k.natAbs ∣ x.natAbs := Int.natAbs_dvd_natAbs.mpr hkx
    have hky' : k.natAbs ∣ y.natAbs := Int.natAbs_dvd_natAbs.mpr hky
    have h : k.natAbs ∣ Int.gcd x y := Nat.dvd_gcd hkx' hky'
    exact Int.natAbs_dvd.mp (by exact_mod_cast h)
  -- Proof by contradiction: get prime p | gcd(w,v)
  by_contra h_ne1
  obtain ⟨p, hp_prime, hp_dvd_gcd⟩ := Nat.exists_prime_and_dvd h_ne1
  -- p | w and p | v (cast via Int.gcd_dvd_left/right)
  have hp_dvd_w : (p : ℤ) ∣ w :=
    dvd_trans (by exact_mod_cast hp_dvd_gcd : (p : ℤ) ∣ ↑(Int.gcd w v)) (Int.gcd_dvd_left w v)
  have hp_dvd_v : (p : ℤ) ∣ v :=
    dvd_trans (by exact_mod_cast hp_dvd_gcd : (p : ℤ) ∣ ↑(Int.gcd w v)) (Int.gcd_dvd_right w v)
  -- p | a+b and p | Phi
  have hp_dvd_ab : (p : ℤ) ∣ a + b :=
    dvd_trans hp_dvd_w ⟨5 ^ 4, by rw [hw]; ring⟩
  have hp_dvd_Phi : (p : ℤ) ∣ a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by
    rw [hPhi]; exact dvd_mul_of_dvd_right hp_dvd_v 5
  -- Phi - 5*a^4 = (-4a^3+3a^2b-2ab^2+b^3)*(a+b) → p | Phi - 5*a^4
  have hp_dvd_split : (p : ℤ) ∣ (a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*a^4 :=
    dvd_trans hp_dvd_ab ⟨-4*a^3+3*a^2*b-2*a*b^2+b^3, by ring⟩
  -- p | 5*a^4
  have hp_dvd_5a4 : (p : ℤ) ∣ 5 * a ^ 4 := by
    have h := dvd_sub hp_dvd_Phi hp_dvd_split
    rwa [show (a^4-a^3*b+a^2*b^2-a*b^3+b^4) -
        ((a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*a^4) = 5*a^4 from by ring] at h
  -- p ∤ a (else p|a and p|a+b → p|b → p|gcd(a,b)=1, contradiction)
  have hp_na : ¬ (p : ℤ) ∣ a := by
    intro hpa
    have hpb : (p : ℤ) ∣ b := by
      have h := dvd_sub hp_dvd_ab hpa; rwa [show a+b-a=b from by ring] at h
    have h1 : (p : ℤ) ∣ ↑(Int.gcd a b) := dvd_igcd _ a b hpa hpb
    rw [h_cop, Nat.cast_one] at h1
    have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have h2 : 2 ≤ (p : ℤ) := by exact_mod_cast hp_prime.two_le
    linarith
  -- p | 5 (from p | 5*a^4 and p ∤ a)
  have hp_dvd_5 : p ∣ 5 := by
    have h_dvd_nat : p ∣ 5 * a.natAbs ^ 4 := by
      have h := Int.natAbs_dvd_natAbs.mpr hp_dvd_5a4
      simp only [Int.natAbs_mul, Int.natAbs_pow] at h
      exact_mod_cast h
    rcases hp_prime.dvd_mul.mp h_dvd_nat with h5 | h4
    · exact h5
    · exfalso; apply hp_na
      have ha_nat : p ∣ a.natAbs := hp_prime.dvd_of_dvd_pow h4
      exact Int.natAbs_dvd_natAbs.mp (by exact_mod_cast ha_nat)
  -- p = 5
  have hp_eq_5 : p = 5 :=
    (Nat.Prime.eq_one_or_self_of_dvd (by decide) p hp_dvd_5).resolve_left hp_prime.one_lt.ne'
  subst hp_eq_5
  -- 5|w → w = 5*w0; 5|v → v = 5*v0
  obtain ⟨w0, hw0⟩ := hp_dvd_w
  obtain ⟨v0, hv0⟩ := hp_dvd_v
  -- a + b = 5^5 * w0
  have hab_55 : a + b = 5 ^ 5 * w0 := by rw [hw, hw0]; ring
  -- 5 | a+b
  have h5_sum : (5 : ℤ) ∣ a + b := ⟨5^4 * w0, by rw [hab_55]; ring⟩
  -- 5^2 | Phi - 5*(ab)^2 since Phi-5*(ab)^2 = (a+b)^4 - 5*(a+b)^2*(ab) and 5^5|a+b
  have h_Phi_mod : (5 : ℤ) ^ 2 ∣ (a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*(a*b)^2 := by
    refine ⟨5^18 * w0^4 - 5^9 * w0^2 * (a*b), ?_⟩
    have heq : a^4-a^3*b+a^2*b^2-a*b^3+b^4 - 5*(a*b)^2 = (a+b)^4 - 5*(a+b)^2*(a*b) := by ring
    rw [heq, hab_55]; ring
  -- 5^2 | Phi (since Phi=5*v=5*(5*v0)=5^2*v0)
  have h52_Phi : (5 : ℤ)^2 ∣ a^4-a^3*b+a^2*b^2-a*b^3+b^4 :=
    ⟨v0, by rw [hPhi, hv0]; ring⟩
  -- 5^2 | 5*(ab)^2 → 5 | (ab)^2
  have h5_ab2 : (5 : ℤ) ∣ (a*b)^2 := by
    have h52 : (5 : ℤ)^2 ∣ 5*(a*b)^2 := by
      have h := dvd_sub h52_Phi h_Phi_mod
      rwa [show (a^4-a^3*b+a^2*b^2-a*b^3+b^4) -
          ((a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*(a*b)^2) = 5*(a*b)^2 from by ring] at h
    obtain ⟨k, hk⟩ := h52
    have h25 : (5:ℤ)^2 = 25 := by norm_num
    have hcanc : 5 * (a*b)^2 = 5 * (5 * k) := by linarith
    exact ⟨k, mul_left_cancel₀ (show (5:ℤ) ≠ 0 from by norm_num) hcanc⟩
  -- 5 | ab (prime 5 | (ab)^2 = ab*ab → 5|ab)
  have h5_ab : (5 : ℤ) ∣ a * b := by
    by_contra h5nab
    exact h5nab (euclid5 (a*b) (a*b) (by rwa [show a*b*(a*b)=(a*b)^2 from by ring]) h5nab)
  -- 5|a or 5|b
  have h5_a_or_b : (5 : ℤ) ∣ a ∨ (5 : ℤ) ∣ b := by
    by_contra h; push_neg at h
    exact h.1 (euclid5 a b h5_ab h.2)
  -- Both cases give 5|a and 5|b, contradicting gcd(a,b)=1
  have aux : (5:ℤ) ∣ a → (5:ℤ) ∣ b → False := fun h5x h5y => by
    have h1 : (5:ℤ) ∣ ↑(Int.gcd a b) := dvd_igcd _ a b h5x h5y
    rw [h_cop, Nat.cast_one] at h1
    exact absurd (Int.le_of_dvd one_pos h1) (by norm_num)
  rcases h5_a_or_b with h5a | h5b
  · apply aux h5a
    have h := dvd_sub h5_sum h5a; rwa [show a+b-a=b from by ring] at h
  · apply aux _ h5b
    have h := dvd_sub h5_sum h5b; rwa [show a+b-b=a from by ring] at h
