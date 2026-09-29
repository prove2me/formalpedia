-- Prove2me | solution 1 for flt5_pow4_dvd_sum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T11:51:30.674619+00:00
-- url     : https://prove2.me/submissions/80072957-d106-42af-a1be-3458b8f63038

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Multiplicity

-- Prove 5^4 | a+b from a^5+b^5=c^5, gcd(a,b)=1, 5|c, c≠0.
-- Elementary argument: Phi = a^4-...-b^4, when a+b=5u: Phi = 5*(a^4-10a^3u+...) = 5v
-- v ≡ a^4 (mod 5), 5∤a → 5∤v. Then u*v = 5^3*c1^5 (from 25*u*v = 5^5*c1^5).
-- gcd(v,5)=1 and 5^3|uv → 5^3|u → 5^4 | 5u = a+b.

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) :
    (5 : ℤ) ^ 4 ∣ a + b := by
  haveI hfact5 : Fact (Nat.Prime 5) := ⟨by decide⟩
  have key5 : ∀ x : ZMod 5, x ^ 5 = x := by decide
  -- 1) 5 | a+b
  have h5ab : (5 : ℤ) ∣ a + b := by
    have heq5 : ((a : ℤ) : ZMod 5) ^ 5 + ((b : ℤ) : ZMod 5) ^ 5 = ((c : ℤ) : ZMod 5) ^ 5 := by
      have := congr_arg (Int.cast : ℤ → ZMod 5) h_eq; push_cast at this; exact this
    have hc0 : ((c : ℤ) : ZMod 5) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h5c
    simp only [key5, hc0, zero_pow (show 5 ≠ 0 from by omega)] at heq5
    have : ((a + b : ℤ) : ZMod 5) = 0 := by push_cast; exact heq5
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  obtain ⟨u, hu⟩ := h5ab
  -- 2) 5 ∤ a
  have h5na : ¬(5 : ℤ) ∣ a := by
    intro h5a
    have h5c5 : (5 : ℤ) ∣ a ^ 5 + b ^ 5 := by rw [h_eq]; exact dvd_pow h5c (by omega)
    have h5a5 : (5 : ℤ) ∣ a ^ 5 := dvd_pow h5a (by omega)
    have h5b5 : (5 : ℤ) ∣ b ^ 5 := by
      have := Int.dvd_sub h5c5 h5a5; simp only [add_sub_cancel_left] at this; exact this
    have h5b : (5 : ℤ) ∣ b := by
      have hzmod : ((b : ℤ) : ZMod 5) ^ 5 = 0 := by
        rw [show ((b:ℤ):ZMod 5)^5 = ((b^5:ℤ):ZMod 5) from by push_cast; ring]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h5b5
      rw [key5] at hzmod; rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzmod
    have h5gcd : (5 : ℕ) ∣ Int.gcd a b := by
      simp only [Int.gcd]
      apply Nat.dvd_gcd
      · obtain ⟨k, hk⟩ := h5a; exact ⟨k.natAbs, by simp [hk, Int.natAbs_mul]⟩
      · obtain ⟨k, hk⟩ := h5b; exact ⟨k.natAbs, by simp [hk, Int.natAbs_mul]⟩
    rw [h_cop] at h5gcd; exact absurd h5gcd (by decide)
  -- 3) Set v = Phi/5 where Phi = a^4-a^3b+a^2b^2-ab^3+b^4
  --    When b = 5u-a: Phi = 5*(a^4 - 10a^3u + 50a^2u^2 - 125au^3 + 125u^4) = 5v
  set v := a ^ 4 - 10 * a ^ 3 * u + 50 * a ^ 2 * u ^ 2 - 125 * a * u ^ 3 + 125 * u ^ 4
  have hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v := by
    show a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 =
        5 * (a ^ 4 - 10 * a ^ 3 * u + 50 * a ^ 2 * u ^ 2 - 125 * a * u ^ 3 + 125 * u ^ 4)
    have hb : b = 5 * u - a := by linarith
    rw [hb]; ring
  -- 4) 5 ∤ v: since v ≡ a^4 (mod 5) and 5∤a
  have hv_dvd : (5 : ℤ) ∣ v - a ^ 4 := by
    show (5:ℤ) ∣ (a^4 - 10*a^3*u + 50*a^2*u^2 - 125*a*u^3 + 125*u^4) - a^4
    exact ⟨-2*a^3*u + 10*a^2*u^2 - 25*a*u^3 + 25*u^4, by ring⟩
  have h5nv : ¬(5 : ℤ) ∣ v := by
    intro h5v
    have h5a4 : (5 : ℤ) ∣ a ^ 4 := by
      have h := Int.dvd_sub h5v hv_dvd
      have heq : v - (v - a^4) = a^4 := by ring
      rwa [heq] at h
    have ha4_0 : ((a : ℤ) : ZMod 5) ^ 4 = 0 := by
      rw [show ((a : ℤ) : ZMod 5) ^ 4 = ((a ^ 4 : ℤ) : ZMod 5) from by push_cast; ring]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h5a4
    have ha_0 : ((a : ℤ) : ZMod 5) = 0 := by
      have h5 : ((a : ℤ) : ZMod 5) ^ 5 = ((a : ℤ) : ZMod 5) := key5 _
      have ha5_0 : ((a : ℤ) : ZMod 5) ^ 5 = 0 :=
        calc ((a : ℤ) : ZMod 5) ^ 5
            = ((a : ℤ) : ZMod 5) * ((a : ℤ) : ZMod 5) ^ 4 := by ring
          _ = ((a : ℤ) : ZMod 5) * 0 := by rw [ha4_0]
          _ = 0 := mul_zero _
      rw [h5] at ha5_0; exact ha5_0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha_0
    exact h5na (by exact_mod_cast ha_0)
  -- 5) c = 5*c1, factorization gives u*v = 5^3*c1^5
  obtain ⟨c1, hc1⟩ := h5c
  have huv : u * v = 5 ^ 3 * c1 ^ 5 := by
    apply mul_left_cancel₀ (show (5:ℤ)^2 ≠ 0 from by decide)
    have hfact : a ^ 5 + b ^ 5 = (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by
      ring
    calc (5:ℤ)^2 * (u * v)
        = (5 * u) * (5 * v) := by ring
      _ = (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by
            rw [show 5 * u = a + b from by linarith, hPhi]
      _ = a ^ 5 + b ^ 5 := hfact.symm
      _ = c ^ 5 := h_eq
      _ = (5 * c1) ^ 5 := by rw [hc1]
      _ = 5^2 * (5^3 * c1^5) := by ring
  -- 6) 5^3 | u (ZMod 5 Euclid via decide, three rounds)
  have mul0_zmod5 : ∀ x y : ZMod 5, x * y = 0 → y ≠ 0 → x = 0 := by decide
  have euclid5 : ∀ x y : ℤ, (5:ℤ) ∣ x * y → ¬(5:ℤ) ∣ y → (5:ℤ) ∣ x := by
    intro x y hxy hny
    have hxy0 : (x : ZMod 5) * (y : ZMod 5) = 0 := by
      have h : ((x * y : ℤ) : ZMod 5) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hxy
      push_cast at h; exact h
    have hy0 : (y : ZMod 5) ≠ 0 := by
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      exact hny (by exact_mod_cast h)
    have hx0 : (x : ZMod 5) = 0 := mul0_zmod5 _ _ hxy0 hy0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0
    exact_mod_cast hx0
  have h53u : (5:ℤ)^3 ∣ u := by
    have h5u : (5:ℤ) ∣ u := euclid5 u v ⟨5^2 * c1^5, by rw [huv]; ring⟩ h5nv
    obtain ⟨u1, hu1⟩ := h5u
    have hu1v : u1 * v = 5^2 * c1^5 := by
      apply mul_left_cancel₀ (show (5:ℤ) ≠ 0 from by decide)
      calc 5 * (u1 * v) = 5 * u1 * v := by ring
        _ = u * v := by rw [← hu1]
        _ = 5^3 * c1^5 := huv
        _ = 5 * (5^2 * c1^5) := by ring
    have h5u1 : (5:ℤ) ∣ u1 := euclid5 u1 v ⟨5 * c1^5, by rw [hu1v]; ring⟩ h5nv
    obtain ⟨u2, hu2⟩ := h5u1
    have hu2v : u2 * v = 5 * c1^5 := by
      apply mul_left_cancel₀ (show (5:ℤ) ≠ 0 from by decide)
      calc 5 * (u2 * v) = 5 * u2 * v := by ring
        _ = u1 * v := by rw [← hu2]
        _ = 5^2 * c1^5 := hu1v
        _ = 5 * (5 * c1^5) := by ring
    have h5u2 : (5:ℤ) ∣ u2 := euclid5 u2 v ⟨c1^5, hu2v⟩ h5nv
    obtain ⟨u3, hu3⟩ := h5u2
    exact ⟨u3, by rw [hu1, hu2, hu3]; ring⟩
  -- 7) 5^4 | a+b = 5*u
  obtain ⟨w, hw⟩ := h53u
  exact ⟨w, by linarith⟩
