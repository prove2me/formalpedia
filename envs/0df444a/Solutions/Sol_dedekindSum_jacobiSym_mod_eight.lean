-- Prove2me | solution 1 for dedekindSum_jacobiSym_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a62ab64f-807b-567b-aef5-113805848c5d

import Definitions.Def_NumberTheory_DedekindSum
import Theorems.Thm_dedekindSum_add_dedekindSum
import Theorems.Thm_exists_intCast_eq_six_mul_dedekindSum
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_dedekindSum_jacobiSym_mod_eight

set_option autoImplicit false

namespace WNPar

private lemma neg_one_pow_div_two (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    ((-1 : ℤ)) ^ (a / 2 * (b / 2)) = if a % 4 = 3 ∧ b % 4 = 3 then -1 else 1 := by
  have h4a : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have h4b : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases h4a with h1 | h1
  · have hev : Even (a / 2) := ⟨a / 4, by omega⟩
    rw [Even.neg_one_pow (hev.mul_right _), if_neg (by simp [h1])]
  · rcases h4b with h2 | h2
    · have hev : Even (b / 2) := ⟨b / 4, by omega⟩
      rw [Even.neg_one_pow (hev.mul_left _), if_neg (by simp [h2])]
    · have ho1 : Odd (a / 2) := ⟨a / 4, by omega⟩
      have ho2 : Odd (b / 2) := ⟨b / 4, by omega⟩
      rw [Odd.neg_one_pow (Nat.odd_mul.mpr ⟨ho1, ho2⟩), if_pos ⟨h1, h2⟩]

private lemma endgame_zmod (x y j : ZMod 8)
    (hx : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7) (hy : y = 1 ∨ y = 3 ∨ y = 5 ∨ y = 7)
    (hj : j = 1 ∨ j = -1) :
    ∀ A : ZMod 8, x * A + y * (x + 1 - 2*j) = x^2 + y^2 + 1 - 3*x*y →
      A = y + 1 - 2*((if (x = 3 ∨ x = 7) ∧ (y = 3 ∨ y = 7) then (-1 : ZMod 8) else 1)*j) := by
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
    rcases hj with rfl|rfl <;> decide

private lemma intCast_zmod8_eq (a : ℤ) (r : ℤ) (h : a % 8 = r % 8) :
    ((a : ZMod 8)) = ((r : ℤ) : ZMod 8) :=
  (ZMod.intCast_eq_intCast_iff a r 8).mpr h

private lemma zmod8_odd_cases (a : ℤ) (ha : a % 2 = 1) :
    (a : ZMod 8) = 1 ∨ (a : ZMod 8) = 3 ∨ (a : ZMod 8) = 5 ∨ (a : ZMod 8) = 7 := by
  have h8 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  rcases h8 with h | h | h | h
  · exact Or.inl (by exact_mod_cast intCast_zmod8_eq a 1 (by omega))
  · exact Or.inr (Or.inl (by exact_mod_cast intCast_zmod8_eq a 3 (by omega)))
  · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast intCast_zmod8_eq a 5 (by omega))))
  · exact Or.inr (Or.inr (Or.inr (by exact_mod_cast intCast_zmod8_eq a 7 (by omega))))

private lemma zmod8_mem37_iff (a : ℤ) (ha : a % 2 = 1) :
    ((a : ZMod 8) = 3 ∨ (a : ZMod 8) = 7) ↔ a % 4 = 3 := by
  constructor
  · rintro (h | h)
    · have := (ZMod.intCast_eq_intCast_iff a 3 8).mp (by exact_mod_cast h)
      unfold Int.ModEq at this; omega
    · have := (ZMod.intCast_eq_intCast_iff a 7 8).mp (by exact_mod_cast h)
      unfold Int.ModEq at this; omega
  · intro h4
    have h8 : a % 8 = 3 ∨ a % 8 = 7 := by omega
    rcases h8 with h | h
    · exact Or.inl (by exact_mod_cast intCast_zmod8_eq a 3 (by omega))
    · exact Or.inr (by exact_mod_cast intCast_zmod8_eq a 7 (by omega))

private lemma odd_step_congruence (x y A B J J' : ℤ)
    (hx2 : x % 2 = 1) (hy2 : y % 2 = 1)
    (hJ' : J' = 1 ∨ J' = -1)
    (hQR : J = (if x % 4 = 3 ∧ y % 4 = 3 then (-1 : ℤ) else 1) * J')
    (hrec : x * A + y * B = x^2 + y^2 + 1 - 3*x*y)
    (hB : B ≡ x + 1 - 2*J' [ZMOD 8]) :
    A ≡ y + 1 - 2*J [ZMOD 8] := by
  have hx8 := zmod8_odd_cases x hx2
  have hy8 := zmod8_odd_cases y hy2
  have hj8 : ((J' : ℤ) : ZMod 8) = 1 ∨ ((J' : ℤ) : ZMod 8) = -1 := by
    rcases hJ' with rfl | rfl
    · exact Or.inl (by push_cast; ring)
    · exact Or.inr (by push_cast; ring)

  have hrec8 : (x : ZMod 8) * (A : ZMod 8) + (y : ZMod 8) * ((x : ZMod 8) + 1 - 2*(J' : ZMod 8))
      = (x : ZMod 8)^2 + (y : ZMod 8)^2 + 1 - 3*(x : ZMod 8)*(y : ZMod 8) := by
    have hB8 : ((B : ℤ) : ZMod 8) = ((x + 1 - 2*J' : ℤ) : ZMod 8) :=
      (ZMod.intCast_eq_intCast_iff _ _ 8).mpr hB
    have h0 := congrArg (Int.cast : ℤ → ZMod 8) hrec
    push_cast at h0 hB8 ⊢
    rw [← hB8]
    linear_combination h0
  have hend := endgame_zmod (x : ZMod 8) (y : ZMod 8) (J' : ZMod 8) hx8 hy8 hj8
    (A : ZMod 8) hrec8

  refine (ZMod.intCast_eq_intCast_iff A (y + 1 - 2*J) 8).mp ?_
  rw [hQR]
  push_cast [apply_ite (Int.cast : ℤ → ZMod 8)]
  rw [if_congr (and_congr (zmod8_mem37_iff x hx2) (zmod8_mem37_iff y hy2)) rfl rfl] at hend
  linear_combination hend

private theorem par_key : ∀ k : ℕ, Odd k → ∀ h : ℕ, Nat.Coprime h k →
    ∃ A : ℤ, (A : ℚ) = 12 * (k : ℚ) * dedekindSum h k ∧
      A ≡ (k : ℤ) + 1 - 2 * jacobiSym h k [ZMOD 8] := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro hk h hco
  rcases eq_or_ne k 1 with rfl | hk1
  · refine ⟨0, ?_, ?_⟩
    · rw [dedekindSum_one_right]; norm_num
    · rw [jacobiSym.one_right]; decide
  have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk
  have hk3 : 3 ≤ k := by omega
  have hkpos : 0 < k := by omega

  have hco' : Nat.Coprime (h % k) k := by
    show Nat.gcd (h % k) k = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact hco
  have hsred : dedekindSum (h : ℤ) k = dedekindSum ((h % k : ℕ) : ℤ) k := by
    conv_lhs => rw [show ((h : ℕ) : ℤ) = ((h % k : ℕ) : ℤ) + ((h / k : ℕ) : ℤ) * (k : ℤ) from by
      exact_mod_cast (Nat.mod_add_div' h k).symm]
    rw [dedekindSum_add_mul]
  have hJred : jacobiSym (h : ℤ) k = jacobiSym ((h % k : ℕ) : ℤ) k := by
    apply jacobiSym.mod_left'
    rw [Int.natCast_mod, Int.emod_emod_of_dvd _ dvd_rfl]

  have odd_case : ∀ h₀ : ℕ, h₀ < k → 0 < h₀ → h₀ % 2 = 1 → Nat.Coprime h₀ k →
      ∃ A : ℤ, (A : ℚ) = 12 * (k : ℚ) * dedekindSum h₀ k ∧
        A ≡ (k : ℤ) + 1 - 2 * jacobiSym h₀ k [ZMOD 8] := by
    intro h₀ hlt hpos₀ hodd₀ hco₀
    obtain ⟨B, hBval, hBmod⟩ := IH h₀ hlt (Nat.odd_iff.mpr hodd₀) k hco₀.symm
    obtain ⟨z, hz⟩ := exists_intCast_eq_six_mul_dedekindSum h₀ k hkpos
    have hAval : ((2 * z : ℤ) : ℚ) = 12 * (k : ℚ) * dedekindSum h₀ k := by
      push_cast at hz ⊢; linarith

    have hq0 : (h₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hqk : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hrec := dedekindSum_add_dedekindSum h₀ k hpos₀ hkpos hco₀
    have hZ : (h₀ : ℤ) * (2 * z) + (k : ℤ) * B
        = (h₀ : ℤ)^2 + (k : ℤ)^2 + 1 - 3 * (h₀ : ℤ) * (k : ℤ) := by
      have h12 : (h₀ : ℚ) * ((2 * z : ℤ) : ℚ) + (k : ℚ) * (B : ℚ)
          = (h₀ : ℚ)^2 + (k : ℚ)^2 + 1 - 3 * (h₀ : ℚ) * (k : ℚ) := by
        rw [hAval, hBval]
        field_simp at hrec
        linear_combination hrec / 4
      exact_mod_cast h12

    have hQR : jacobiSym (h₀ : ℤ) k
        = (if (h₀ : ℤ) % 4 = 3 ∧ (k : ℤ) % 4 = 3 then (-1 : ℤ) else 1)
          * jacobiSym (k : ℤ) h₀ := by
      rw [jacobiSym.quadratic_reciprocity (Nat.odd_iff.mpr hodd₀) hk,
        neg_one_pow_div_two h₀ k hodd₀ hk2]
      congr 1
      exact if_congr ⟨fun hh => by omega, fun hh => by omega⟩ rfl rfl
    have hJ'pm : jacobiSym (k : ℤ) h₀ = 1 ∨ jacobiSym (k : ℤ) h₀ = -1 :=
      jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact hco₀.symm)
    refine ⟨2 * z, hAval, ?_⟩
    exact odd_step_congruence (h₀ : ℤ) (k : ℤ) (2 * z) B _ _
      (by omega) (by omega) hJ'pm hQR hZ hBmod

  rcases Nat.eq_zero_or_pos (h % k) with hz0 | hpos
  · exfalso
    rw [hz0] at hco'
    have := (Nat.coprime_zero_left k).mp hco'
    omega
  have hlt : h % k < k := Nat.mod_lt h hkpos
  rcases Nat.even_or_odd (h % k) with heven | hoddh
  ·
    have hodd'' : (k - h % k) % 2 = 1 := by
      rcases heven with ⟨m, hm⟩; omega
    have hlt'' : k - h % k < k := by omega
    have hpos'' : 0 < k - h % k := by omega
    have hco'' : Nat.Coprime (k - h % k) k := by
      show Nat.gcd (k - h % k) k = 1
      have h1 : Nat.gcd (k - h % k) k ∣ h % k := by
        have hd := Nat.dvd_sub (Nat.gcd_dvd_right (k - h % k) k) (Nat.gcd_dvd_left (k - h % k) k)
        rwa [show k - (k - h % k) = h % k from by omega] at hd
      have h2 : Nat.gcd (k - h % k) k ∣ 1 := by
        have := Nat.dvd_gcd h1 (Nat.gcd_dvd_right (k - h % k) k)
        rwa [hco'] at this
      exact Nat.dvd_one.mp h2
    obtain ⟨A'', hAval'', hAmod''⟩ := odd_case (k - h % k) hlt'' hpos'' hodd'' hco''

    have hsflip : dedekindSum ((k - h % k : ℕ) : ℤ) k = -dedekindSum ((h % k : ℕ) : ℤ) k := by
      rw [show ((k - h % k : ℕ) : ℤ) = -((h % k : ℕ) : ℤ) + 1 * (k : ℤ) from by push_cast; omega,
        dedekindSum_add_mul, dedekindSum_neg]
    have hJflip : jacobiSym ((k - h % k : ℕ) : ℤ) k
        = ZMod.χ₄ (k : ZMod 4) * jacobiSym ((h % k : ℕ) : ℤ) k := by
      have hmod : ((k - h % k : ℕ) : ℤ) % (k : ℤ) = (-((h % k : ℕ) : ℤ)) % (k : ℤ) := by
        have : ((k - h % k : ℕ) : ℤ) ≡ -((h % k : ℕ) : ℤ) [ZMOD (k : ℤ)] :=
          Int.modEq_iff_dvd.2 ⟨-1, by push_cast; ring_nf; omega⟩
        exact this
      rw [jacobiSym.mod_left' hmod, jacobiSym.neg _ hk]

    have hJpm : jacobiSym ((h % k : ℕ) : ℤ) k = 1 ∨ jacobiSym ((h % k : ℕ) : ℤ) k = -1 :=
      jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact hco')
    have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by omega
    have hχ : ZMod.χ₄ (k : ZMod 4) = if k % 4 = 1 then 1 else -1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega)]
    refine ⟨-A'', ?_, ?_⟩
    · rw [hsred]
      rw [hsflip] at hAval''
      push_cast at hAval'' ⊢
      linarith
    · rw [hJred]
      rw [hJflip, hχ] at hAmod''
      rcases hJpm with hJ1 | hJ1 <;> rw [hJ1] at hAmod'' ⊢
      · rcases hk4 with h4 | h4
        · rw [if_pos h4] at hAmod''
          unfold Int.ModEq at hAmod'' ⊢; omega
        · rw [if_neg (by omega)] at hAmod''
          unfold Int.ModEq at hAmod'' ⊢; omega
      · rcases hk4 with h4 | h4
        · rw [if_pos h4] at hAmod''
          unfold Int.ModEq at hAmod'' ⊢; omega
        · rw [if_neg (by omega)] at hAmod''
          unfold Int.ModEq at hAmod'' ⊢; omega
  ·
    obtain ⟨A, hAval, hAmod⟩ := odd_case (h % k) hlt hpos (Nat.odd_iff.mp hoddh) hco'
    refine ⟨A, ?_, ?_⟩
    · rw [hsred]; exact hAval
    · rw [hJred]; exact hAmod

end WNPar

theorem solution (h k : ℕ) (hk : Odd k) (hhk : Nat.Coprime h k) : ∃ t : ℤ, 12 * (k : ℚ) * dedekindSum h k = (k : ℚ) + 1 - 2 * ((jacobiSym h k : ℤ) : ℚ) + 8 * t := by
  obtain ⟨A, hval, hmod⟩ := WNPar.par_key k hk h hhk
  have h8 : (8 : ℤ) ∣ ((k : ℤ) + 1 - 2 * jacobiSym h k) - A := Int.ModEq.dvd hmod
  obtain ⟨t, ht⟩ := h8
  refine ⟨-t, ?_⟩
  rw [← hval]
  have := congrArg (Int.cast : ℤ → ℚ) ht
  push_cast at this ⊢
  linarith

end S_dedekindSum_jacobiSym_mod_eight
end P2MW
export P2MW.S_dedekindSum_jacobiSym_mod_eight (solution)
