-- Prove2me | solution 1 for diophantine_triple_non_euler_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T07:02:28.753994+00:00
-- url     : https://prove2.me/submissions/66d2e188-00cb-40ec-aa7d-db13c9e29e6d

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ByContra
import Mathlib.Data.Int.Basic
import Definitions.Def_diophantine_descent

set_option autoImplicit false

open DiophantineDescent

/-- Auxiliary: `a^2 + 1` is never a square for `1 ≤ a`. -/
theorem jones_nonsq_succ (a : Nat) (ha : 1 ≤ a) : ¬ ∃ k : Nat, a ^ 2 + 1 = k ^ 2 := by
  rintro ⟨k, hk⟩
  have h1 : a < k := by
    rcases lt_or_ge a k with h | h
    · exact h
    · exfalso
      have hle2 : k ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left h 2
      omega
  have h2 : k < a + 1 := by
    rcases lt_or_ge k (a + 1) with h | h
    · exact h
    · exfalso
      have hle2 : (a + 1) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left h 2
      have hexpand : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
      omega
  omega

/-- Pure Nat square-product inequality: the engine behind `d_- < max`. -/
theorem jones_sq_bound (x y z : Nat) (hx0 : 0 < x) (hy0 : 0 < y) (_hz0 : 0 < z)
    (hx4 : x < 4 * z) (hy4 : y < 4 * z) :
    (x + y + 2 * x * y * z) ^ 2 < 4 * (x * y + 1) * (x * z + 1) * (y * z + 1) := by
  have hx2 : x ^ 2 < 4 * x * z := by
    have hmul : x * x < x * (4 * z) := mul_lt_mul_of_pos_left hx4 hx0
    calc x ^ 2 = x * x := by ring
      _ < x * (4 * z) := hmul
      _ = 4 * x * z := by ring
  have hy2 : y ^ 2 < 4 * y * z := by
    have hmul : y * y < y * (4 * z) := mul_lt_mul_of_pos_left hy4 hy0
    calc y ^ 2 = y * y := by ring
      _ < y * (4 * z) := hmul
      _ = 4 * y * z := by ring
  have heq : 4 * (x * y + 1) * (x * z + 1) * (y * z + 1) + (x ^ 2 + y ^ 2)
      = (x + y + 2 * x * y * z) ^ 2
        + (4 * x * y * z ^ 2 + 2 * x * y + 4 * x * z + 4 * y * z + 4) := by ring
  have hExtra : x ^ 2 + y ^ 2
      < 4 * x * y * z ^ 2 + 2 * x * y + 4 * x * z + 4 * y * z + 4 := by
    omega
  omega

/-- From strict squares to strict base (Int, nonnegative RHS). -/
theorem jones_base_lt (X Y : Int) (hY : 0 ≤ Y) (h : X ^ 2 < Y ^ 2) : X < Y := by
  rcases lt_or_ge X Y with hlt | hge
  · exact hlt
  · exfalso
    have hle2 : Y ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hY hge 2
    linarith

/-- Descent-free form of `d_- < max`: with square roots as data. -/
theorem jones_dminus_lt (x y z u v w : Nat) (hx0 : 0 < x) (hy0 : 0 < y) (_hz0 : 0 < z)
    (hx4 : x < 4 * z) (hy4 : y < 4 * z)
    (hxy : u ^ 2 = x * y + 1) (hxz : v ^ 2 = x * z + 1) (hyz : w ^ 2 = y * z + 1) :
    (x : Int) + (y : Int) + 2 * (x : Int) * (y : Int) * (z : Int)
      < 2 * (u : Int) * (v : Int) * (w : Int) := by
  have hN := jones_sq_bound x y z hx0 hy0 _hz0 hx4 hy4
  have huI : (u : Int) ^ 2 = (x : Int) * (y : Int) + 1 := by exact_mod_cast hxy
  have hvI : (v : Int) ^ 2 = (x : Int) * (z : Int) + 1 := by exact_mod_cast hxz
  have hwI : (w : Int) ^ 2 = (y : Int) * (z : Int) + 1 := by exact_mod_cast hyz
  have eW : (2 * (u : Int) * (v : Int) * (w : Int)) ^ 2
      = 4 * ((x : Int) * (y : Int) + 1)
        * (((x : Int) * (z : Int) + 1) * ((y : Int) * (z : Int) + 1)) := by
    have h1 : (2 * (u : Int) * (v : Int) * (w : Int)) ^ 2
        = 4 * (u : Int) ^ 2 * ((v : Int) ^ 2 * (w : Int) ^ 2) := by ring
    rw [h1, huI, hvI, hwI]
  have ecast : (((4 * (x * y + 1) * (x * z + 1) * (y * z + 1) : Nat)) : Int)
      = 4 * ((x : Int) * (y : Int) + 1)
        * (((x : Int) * (z : Int) + 1) * ((y : Int) * (z : Int) + 1)) := by
    push_cast
    ring
  have hI : ((((x + y + 2 * x * y * z) ^ 2 : Nat)) : Int)
      < ((((4 * (x * y + 1) * (x * z + 1) * (y * z + 1) : Nat))) : Int) := by
    exact_mod_cast hN
  rw [Nat.cast_pow, ecast, ← eW] at hI
  have hsplit : (((x + y + 2 * x * y * z : Nat)) : Int)
      = (x : Int) + (y : Int) + 2 * (x : Int) * (y : Int) * (z : Int) := by
    push_cast
    ring
  rw [hsplit] at hI
  apply jones_base_lt _ _ _ hI
  positivity

/-- Small order facts, proved in a tiny context (keeps `omega` fast). -/
theorem jones_order (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    0 < y ∧ x < 4 * z ∧ y < 4 * z := by
  omega

/-- Final assembly, kept in a tiny context so `linarith` stays fast. -/
theorem jones_finish (A B C M R S T : Int)
    (hA : 0 < A) (hB : 0 < B) (hM : 0 < M)
    (hBC : B < C) (hmC : M < C)
    (hor : C - A - B - M - 2 * A * B * M = 2 * R * S * T
      ∨ C - A - B - M - 2 * A * B * M = -(2 * R * S * T))
    (hlt : (A + B + M + 2 * A * B * M - 2 * R * S * T < B)
      ∨ (A + B + M + 2 * A * B * M - 2 * R * S * T < M))
    (hW : A * B * M < R * S * T)
    (h4 : 4 * (A * B) * 1 ≤ 4 * (A * B) * M) :
    4 * (A * B) < C := by
  have hAB : (0 : Int) ≤ 4 * (A * B) := by
    have g1 : (0 : Int) ≤ A * B := mul_nonneg (le_of_lt hA) (le_of_lt hB)
    exact mul_nonneg (by norm_num) g1
  rcases hor with hplus | hminus
  · linarith
  · exfalso
    rcases hlt with h1 | h1 <;> linarith

theorem solution (a b c : Nat)
    (ht : Triple a b c) (hne : ¬ Euler a b c) : 4 * a * b < c := by
  obtain ⟨ha, hab, hbc, ⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ := ht
  have hrI : (a : Int) * (b : Int) + 1 = (r : Int) ^ 2 := by exact_mod_cast hr
  have hsI : (a : Int) * (c : Int) + 1 = (s : Int) ^ 2 := by exact_mod_cast hs
  have htI : (b : Int) * (c : Int) + 1 = (t : Int) ^ 2 := by exact_mod_cast ht
  have haI : (0 : Int) < (a : Int) := by exact_mod_cast ha
  have habI : (a : Int) < (b : Int) := by exact_mod_cast hab
  have hbcI : (b : Int) < (c : Int) := by exact_mod_cast hbc
  have hrs2 : ((r : Int) * (s : Int)) ^ 2
      = ((a : Int) * (b : Int) + 1) * ((a : Int) * (c : Int) + 1) := by
    rw [mul_pow, ← hrI, ← hsI]
  have hat2 : ((a : Int) * (t : Int)) ^ 2
      = (a : Int) ^ 2 * ((b : Int) * (c : Int) + 1) := by
    rw [mul_pow, ← htI]
  have hbt2 : ((b : Int) * (s : Int)) ^ 2
      = (b : Int) ^ 2 * ((a : Int) * (c : Int) + 1) := by
    rw [mul_pow, ← hsI]
  have hrt2 : ((r : Int) * (t : Int)) ^ 2
      = ((a : Int) * (b : Int) + 1) * ((b : Int) * (c : Int) + 1) := by
    rw [mul_pow, ← hrI, ← htI]
  have hst2 : ((s : Int) * (t : Int)) ^ 2
      = ((a : Int) * (c : Int) + 1) * ((b : Int) * (c : Int) + 1) := by
    rw [mul_pow, ← hsI, ← htI]
  have hcr2 : ((c : Int) * (r : Int)) ^ 2
      = (c : Int) ^ 2 * ((a : Int) * (b : Int) + 1) := by
    rw [mul_pow, ← hrI]
  -- Vieta identities with explicit S, P, M.
  have hAM : (a : Int)
      * ((a : Int) + (b : Int) + (c : Int) + 2 * (a : Int) * (b : Int) * (c : Int)
        - 2 * (r : Int) * (s : Int) * (t : Int)) + 1
      = ((r : Int) * (s : Int) - (a : Int) * (t : Int)) ^ 2 := by
    have hexpand : ((r : Int) * (s : Int) - (a : Int) * (t : Int)) ^ 2
        = ((r : Int) * (s : Int)) ^ 2 + ((a : Int) * (t : Int)) ^ 2
          - 2 * (a : Int) * ((r : Int) * (s : Int) * (t : Int)) := by ring
    rw [hexpand, hrs2, hat2]; ring
  have hBM : (b : Int)
      * ((a : Int) + (b : Int) + (c : Int) + 2 * (a : Int) * (b : Int) * (c : Int)
        - 2 * (r : Int) * (s : Int) * (t : Int)) + 1
      = ((r : Int) * (t : Int) - (b : Int) * (s : Int)) ^ 2 := by
    have hexpand : ((r : Int) * (t : Int) - (b : Int) * (s : Int)) ^ 2
        = ((r : Int) * (t : Int)) ^ 2 + ((b : Int) * (s : Int)) ^ 2
          - 2 * (b : Int) * ((r : Int) * (s : Int) * (t : Int)) := by ring
    rw [hexpand, hrt2, hbt2]; ring
  have hCM : (c : Int)
      * ((a : Int) + (b : Int) + (c : Int) + 2 * (a : Int) * (b : Int) * (c : Int)
        - 2 * (r : Int) * (s : Int) * (t : Int)) + 1
      = ((s : Int) * (t : Int) - (c : Int) * (r : Int)) ^ 2 := by
    have hexpand : ((s : Int) * (t : Int) - (c : Int) * (r : Int)) ^ 2
        = ((s : Int) * (t : Int)) ^ 2 + ((c : Int) * (r : Int)) ^ 2
          - 2 * (c : Int) * ((r : Int) * (s : Int) * (t : Int)) := by ring
    rw [hexpand, hst2, hcr2]; ring
  -- Key Nat inequality via ring identity + omega (no nlinarith).
  have hsqA : a ^ 2 < 4 * a * c := by
    have hlt : a < 4 * c := by omega
    have hmul : a * a < a * (4 * c) := mul_lt_mul_of_pos_left hlt ha
    calc a ^ 2 = a * a := by ring
      _ < a * (4 * c) := hmul
      _ = 4 * a * c := by ring
  have hsqB : b ^ 2 < 4 * b * c := by
    have hlt : b < 4 * c := by omega
    have hpos : 0 < b := by omega
    have hmul : b * b < b * (4 * c) := mul_lt_mul_of_pos_left hlt hpos
    calc b ^ 2 = b * b := by ring
      _ < b * (4 * c) := hmul
      _ = 4 * b * c := by ring
  have heq : 4 * (a * b + 1) * (a * c + 1) * (b * c + 1) + a ^ 2 + b ^ 2
      = (a + b + 2 * a * b * c) ^ 2
        + (4 * a * b * c ^ 2 + 2 * a * b + 4 * a * c + 4 * b * c + 4) := by ring
  have hExtra : a ^ 2 + b ^ 2
      < 4 * a * b * c ^ 2 + 2 * a * b + 4 * a * c + 4 * b * c + 4 := by
    omega
  have hcsq : (a + b + 2 * a * b * c) ^ 2
      < 4 * (a * b + 1) * (a * c + 1) * (b * c + 1) := by
    omega
  -- Transfer to Int squares inequality.
  have hsq1 : (((a + b + 2 * a * b * c : Nat)) : Int) ^ 2
      < (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2 := by
    have e1 : ((((a + b + 2 * a * b * c : Nat))) : Int) ^ 2
        = (((a + b + 2 * a * b * c : Nat) ^ 2 : Nat) : Int) := by push_cast; ring
    have e2 : (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2
        = ((4 * (a * b + 1) * (a * c + 1) * (b * c + 1) : Nat) : Int) := by
      have g : (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2
          = 4 * ((r : Int) ^ 2) * (((s : Int) * (t : Int)) ^ 2) := by ring
      rw [g, hst2, ← hrI]
      push_cast; ring
    rw [e1, e2]
    exact_mod_cast hcsq
  -- From squares to base via monotonicity (no nlinarith).
  have hbase : (((a + b + 2 * a * b * c : Nat)) : Int)
      < 2 * (r : Int) * (s : Int) * (t : Int) := by
    rcases lt_or_ge (((a + b + 2 * a * b * c : Nat)) : Int)
      (2 * (r : Int) * (s : Int) * (t : Int)) with h | h
    · exact h
    · exfalso
      have hYnn : (0 : Int) ≤ 2 * (r : Int) * (s : Int) * (t : Int) := by positivity
      have hle2 : (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2
          ≤ ((((a + b + 2 * a * b * c : Nat))) : Int) ^ 2 :=
        pow_le_pow_left₀ hYnn h 2
      linarith
  have hMltc : (a : Int) + (b : Int) + (c : Int)
      + 2 * (a : Int) * (b : Int) * (c : Int)
      - 2 * (r : Int) * (s : Int) * (t : Int) < (c : Int) := by
    have hcast : (((a + b + 2 * a * b * c : Nat)) : Int)
        = (a : Int) + (b : Int) + 2 * (a : Int) * (b : Int) * (c : Int) := by
      push_cast; ring
    linarith
  -- Nonnegativity of M.
  have hMnonneg : (0 : Int) ≤ (a : Int) + (b : Int) + (c : Int)
      + 2 * (a : Int) * (b : Int) * (c : Int)
      - 2 * (r : Int) * (s : Int) * (t : Int) := by
    rcases lt_or_ge ((a : Int) + (b : Int) + (c : Int)
      + 2 * (a : Int) * (b : Int) * (c : Int)
      - 2 * (r : Int) * (s : Int) * (t : Int)) (0 : Int) with hlt | hnonneg
    · exfalso
      have hsqnn : (0 : Int)
          ≤ ((s : Int) * (t : Int) - (c : Int) * (r : Int)) ^ 2 := sq_nonneg _
      rw [← hCM] at hsqnn
      have hc3 : (3 : Int) ≤ (c : Int) := by exact_mod_cast (by omega : 3 ≤ c)
      have h1 : (1 : Int) ≤ -((a : Int) + (b : Int) + (c : Int)
          + 2 * (a : Int) * (b : Int) * (c : Int)
          - 2 * (r : Int) * (s : Int) * (t : Int)) := by linarith
      have h3 : (3 : Int) * 1
          ≤ (c : Int) * (-((a : Int) + (b : Int) + (c : Int)
            + 2 * (a : Int) * (b : Int) * (c : Int)
            - 2 * (r : Int) * (s : Int) * (t : Int))) :=
        mul_le_mul hc3 h1 (by norm_num) (by linarith)
      have hle : (c : Int) * ((a : Int) + (b : Int) + (c : Int)
          + 2 * (a : Int) * (b : Int) * (c : Int)
          - 2 * (r : Int) * (s : Int) * (t : Int)) ≤ -3 := by linarith
      linarith
    · exact hnonneg
  -- Difference-of-squares identity.
  have eP : (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2
      = 4 * ((a : Int) * (b : Int) + 1)
        * (((a : Int) * (c : Int) + 1) * ((b : Int) * (c : Int) + 1)) := by
    have h1 : (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2
        = 4 * (r : Int) ^ 2 * (((s : Int) * (t : Int)) ^ 2) := by ring
    rwa [hst2, ← hrI] at h1
  have eR : (2 * (r : Int)) ^ 2 = 4 * ((a : Int) * (b : Int) + 1) := by
    have h1 : (2 * (r : Int)) ^ 2 = 4 * (r : Int) ^ 2 := by ring
    rwa [← hrI] at h1
  have key : ((a : Int) + (b : Int) + (c : Int)
        + 2 * (a : Int) * (b : Int) * (c : Int)) ^ 2
        - (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2
      = ((c : Int) - (a : Int) - (b : Int)) ^ 2 - (2 * (r : Int)) ^ 2 := by
    rw [eP, eR]; ring
  have hMne : (a : Int) + (b : Int) + (c : Int)
      + 2 * (a : Int) * (b : Int) * (c : Int)
      - 2 * (r : Int) * (s : Int) * (t : Int) ≠ 0 := by
    intro hzero
    have hSP : (a : Int) + (b : Int) + (c : Int)
        + 2 * (a : Int) * (b : Int) * (c : Int)
        = 2 * (r : Int) * (s : Int) * (t : Int) := by linarith
    have hsqeq : ((a : Int) + (b : Int) + (c : Int)
        + 2 * (a : Int) * (b : Int) * (c : Int)) ^ 2
        = (2 * (r : Int) * (s : Int) * (t : Int)) ^ 2 := by rw [hSP]
    have hUeq : ((c : Int) - (a : Int) - (b : Int)) ^ 2
        = (2 * (r : Int)) ^ 2 := by linarith [key, hsqeq]
    have hor : (c : Int) - (a : Int) - (b : Int) = 2 * (r : Int)
        ∨ (c : Int) - (a : Int) - (b : Int) = -(2 * (r : Int)) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp hUeq
    have har : (a : Int) < 2 * (r : Int) := by
      have e2 : (2 * (r : Int)) ^ 2 = 4 * ((a : Int) * (b : Int) + 1) := eR
      have h4b : (a : Int) < 4 * (b : Int) := by linarith [haI, habI]
      have hmul : (a : Int) * (a : Int) < (a : Int) * (4 * (b : Int)) :=
        mul_lt_mul_of_pos_left h4b haI
      have hlt2 : (a : Int) ^ 2 < (2 * (r : Int)) ^ 2 := by
        rw [e2]
        calc (a : Int) ^ 2 = (a : Int) * (a : Int) := by ring
          _ < (a : Int) * (4 * (b : Int)) := hmul
          _ < 4 * ((a : Int) * (b : Int) + 1) := by linarith
      rcases lt_or_ge ((a : Int)) (2 * (r : Int)) with h | h
      · exact h
      · exfalso
        have hRnn : (0 : Int) ≤ 2 * (r : Int) := by positivity
        have hle2 : (2 * (r : Int)) ^ 2 ≤ (a : Int) ^ 2 :=
          pow_le_pow_left₀ hRnn h 2
        linarith
    rcases hor with hcase | hcase
    · apply hne
      refine ⟨r, hr, ?_⟩
      have hcasteq : (c : Int) = (a : Int) + (b : Int) + 2 * (r : Int) := by
        linarith
      have hc2 : c = a + b + 2 * r := by exact_mod_cast hcasteq
      exact hc2
    · have hcasteq : (c : Int) = (a : Int) + (b : Int) - 2 * (r : Int) := by
        linarith
      linarith
  have hMpos : (0 : Int) < (a : Int) + (b : Int) + (c : Int)
      + 2 * (a : Int) * (b : Int) * (c : Int)
      - 2 * (r : Int) * (s : Int) * (t : Int) :=
    lt_of_le_of_ne hMnonneg (Ne.symm hMne)
  have hPle : 2 * r * s * t ≤ a + b + c + 2 * a * b * c := by
    have hcast : ((2 * r * s * t : Nat) : Int)
        ≤ ((a + b + c + 2 * a * b * c : Nat) : Int) := by
      have e1 : ((2 * r * s * t : Nat) : Int)
          = 2 * (r : Int) * (s : Int) * (t : Int) := by push_cast; ring
      have e2 : ((a + b + c + 2 * a * b * c : Nat) : Int)
          = (a : Int) + (b : Int) + (c : Int)
            + 2 * (a : Int) * (b : Int) * (c : Int) := by push_cast; ring
      rw [e1, e2]
      linarith
    exact_mod_cast hcast
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hPle
  have hm' : m + 2 * r * s * t = a + b + c + 2 * a * b * c := by omega
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hzero | hposm
    · exfalso
      subst hzero
      simp at hm'
      have hcast : 2 * (r : Int) * (s : Int) * (t : Int)
          = (a : Int) + (b : Int) + (c : Int)
            + 2 * (a : Int) * (b : Int) * (c : Int) := by
        have e1 : ((2 * r * s * t : Nat) : Int)
            = 2 * (r : Int) * (s : Int) * (t : Int) := by push_cast; ring
        have e2 : ((a + b + c + 2 * a * b * c : Nat) : Int)
            = (a : Int) + (b : Int) + (c : Int)
              + 2 * (a : Int) * (b : Int) * (c : Int) := by push_cast; ring
        have hcc : ((2 * r * s * t : Nat) : Int)
            = ((a + b + c + 2 * a * b * c : Nat) : Int) := by exact_mod_cast hm'
        rw [e1, e2] at hcc
        linarith
      apply hMne
      linarith
    · exact hposm
  have hmc : m < c := by
    have hcast : ((m : Int)) < (c : Int) := by
      have e1 : ((m : Int))
          = (a : Int) + (b : Int) + (c : Int)
            + 2 * (a : Int) * (b : Int) * (c : Int)
            - 2 * (r : Int) * (s : Int) * (t : Int) := by
        have em : ((m : Nat) : Int) + ((2 * r * s * t : Nat) : Int)
            = ((a + b + c + 2 * a * b * c : Nat) : Int) := by exact_mod_cast hm'
        have e1 : ((2 * r * s * t : Nat) : Int)
            = 2 * (r : Int) * (s : Int) * (t : Int) := by push_cast; ring
        have e2 : ((a + b + c + 2 * a * b * c : Nat) : Int)
            = (a : Int) + (b : Int) + (c : Int)
              + 2 * (a : Int) * (b : Int) * (c : Int) := by push_cast; ring
        rw [e1, e2] at em
        linarith
      rw [e1]
      exact hMltc
    exact_mod_cast hcast
  have hmE : ((m : Nat) : Int)
      = (a : Int) + (b : Int) + (c : Int)
        + 2 * (a : Int) * (b : Int) * (c : Int)
        - 2 * (r : Int) * (s : Int) * (t : Int) := by
    have em : ((m : Nat) : Int) + ((2 * r * s * t : Nat) : Int)
        = ((a + b + c + 2 * a * b * c : Nat) : Int) := by exact_mod_cast hm'
    have e1 : ((2 * r * s * t : Nat) : Int)
        = 2 * (r : Int) * (s : Int) * (t : Int) := by push_cast; ring
    have e2 : ((a + b + c + 2 * a * b * c : Nat) : Int)
        = (a : Int) + (b : Int) + (c : Int)
          + 2 * (a : Int) * (b : Int) * (c : Int) := by push_cast; ring
    rw [e1, e2] at em
    linarith
  have hamI : (a : Int) * ((m : Nat) : Int) + 1
      = ((r : Int) * (s : Int) - (a : Int) * (t : Int)) ^ 2 := by
    rw [hmE]; exact hAM
  have hbmI : (b : Int) * ((m : Nat) : Int) + 1
      = ((r : Int) * (t : Int) - (b : Int) * (s : Int)) ^ 2 := by
    rw [hmE]; exact hBM
  have ham : ∃ k : Nat, a * m + 1 = k ^ 2 := by
    refine ⟨((r : Int) * (s : Int) - (a : Int) * (t : Int)).natAbs, ?_⟩
    have hcast : (((a * m + 1 : Nat)) : Int)
        = ((r : Int) * (s : Int) - (a : Int) * (t : Int)) ^ 2 := by
      push_cast
      linarith [hamI]
    have hnab : (((((r : Int) * (s : Int)
        - (a : Int) * (t : Int)).natAbs ^ 2 : Nat)) : Int)
        = ((r : Int) * (s : Int) - (a : Int) * (t : Int)) ^ 2 := by
      rw [Nat.cast_pow, Int.natAbs_pow_two]
    have hcc : (((a * m + 1 : Nat)) : Int)
        = (((((r : Int) * (s : Int)
          - (a : Int) * (t : Int)).natAbs ^ 2 : Nat)) : Int) := by
      rw [hnab]
      exact hcast
    exact_mod_cast hcc
  have hbm : ∃ k : Nat, b * m + 1 = k ^ 2 := by
    refine ⟨((r : Int) * (t : Int) - (b : Int) * (s : Int)).natAbs, ?_⟩
    have hcast : (((b * m + 1 : Nat)) : Int)
        = ((r : Int) * (t : Int) - (b : Int) * (s : Int)) ^ 2 := by
      push_cast
      linarith [hbmI]
    have hnab : (((((r : Int) * (t : Int)
        - (b : Int) * (s : Int)).natAbs ^ 2 : Nat)) : Int)
        = ((r : Int) * (t : Int) - (b : Int) * (s : Int)) ^ 2 := by
      rw [Nat.cast_pow, Int.natAbs_pow_two]
    have hcc : (((b * m + 1 : Nat)) : Int)
        = (((((r : Int) * (t : Int)
          - (b : Int) * (s : Int)).natAbs ^ 2 : Nat)) : Int) := by
      rw [hnab]
      exact hcast
    exact_mod_cast hcc
  have hmnea : m ≠ a := by
    intro heq
    obtain ⟨k, hk⟩ := ham
    have hkk : a * a + 1 = k ^ 2 := heq ▸ hk
    have hsq : a ^ 2 + 1 = k ^ 2 := by
      calc a ^ 2 + 1 = a * a + 1 := by ring
        _ = k ^ 2 := hkk
    exact jones_nonsq_succ a (by omega) ⟨k, hsq⟩
  have hmneb : m ≠ b := by
    intro heq
    obtain ⟨k, hk⟩ := hbm
    have hkk : b * b + 1 = k ^ 2 := heq ▸ hk
    have hsq : b ^ 2 + 1 = k ^ 2 := by
      calc b ^ 2 + 1 = b * b + 1 := by ring
        _ = k ^ 2 := hkk
    exact jones_nonsq_succ b (by omega) ⟨k, hsq⟩
  -- Nat square roots for the descent value.
  obtain ⟨s1, hs1⟩ := ham
  obtain ⟨t1, ht1⟩ := hbm
  have hs1I : (s1 : Int) ^ 2 = (a : Int) * (m : Int) + 1 := by
    have h : ((a * m + 1 : Nat) : Int) = ((s1 ^ 2 : Nat) : Int) := by
      exact_mod_cast hs1
    push_cast at h
    exact h.symm
  have ht1I : (t1 : Int) ^ 2 = (b : Int) * (m : Int) + 1 := by
    have h : ((b * m + 1 : Nat) : Int) = ((t1 ^ 2 : Nat) : Int) := by
      exact_mod_cast ht1
    push_cast at h
    exact h.symm
  -- The involution identity: c is the `d_+` of (a, b, m).
  have eW2 : ((r : Int) * (s : Int) * (t : Int)) ^ 2
      = ((a : Int) * (b : Int) + 1)
        * (((a : Int) * (c : Int) + 1) * ((b : Int) * (c : Int) + 1)) := by
    have h1 : ((r : Int) * (s : Int) * (t : Int)) ^ 2
        = (r : Int) ^ 2 * ((s : Int) ^ 2 * (t : Int) ^ 2) := by ring
    rw [h1, ← hrI, ← hsI, ← htI]
  have hΔ : ((c : Int) - (a : Int) - (b : Int) - (m : Int)
        - 2 * (a : Int) * (b : Int) * (m : Int)) ^ 2
        - 4 * ((a : Int) * (b : Int) + 1)
          * (((a : Int) * (m : Int) + 1) * ((b : Int) * (m : Int) + 1))
      = 4 * (((r : Int) * (s : Int) * (t : Int)) ^ 2
        - ((a : Int) * (b : Int) + 1)
          * (((a : Int) * (c : Int) + 1) * ((b : Int) * (c : Int) + 1))) := by
    rw [hmE]; ring
  rw [eW2] at hΔ
  simp only [sub_self, mul_zero] at hΔ
  have keyInvSq : ((c : Int) - (a : Int) - (b : Int) - (m : Int)
        - 2 * (a : Int) * (b : Int) * (m : Int)) ^ 2
      = (2 * (r : Int) * (s1 : Int) * (t1 : Int)) ^ 2 := by
    have eRHS : (2 * (r : Int) * (s1 : Int) * (t1 : Int)) ^ 2
        = 4 * ((a : Int) * (b : Int) + 1)
          * (((a : Int) * (m : Int) + 1) * ((b : Int) * (m : Int) + 1)) := by
      have h1 : (2 * (r : Int) * (s1 : Int) * (t1 : Int)) ^ 2
          = 4 * (r : Int) ^ 2 * ((s1 : Int) ^ 2 * (t1 : Int) ^ 2) := by ring
      rw [h1, ← hrI, ← hs1I, ← ht1I]
    linarith [hΔ, eRHS]
  have hor : (c : Int) - (a : Int) - (b : Int) - (m : Int)
        - 2 * (a : Int) * (b : Int) * (m : Int)
        = 2 * (r : Int) * (s1 : Int) * (t1 : Int)
      ∨ (c : Int) - (a : Int) - (b : Int) - (m : Int)
        - 2 * (a : Int) * (b : Int) * (m : Int)
        = -(2 * (r : Int) * (s1 : Int) * (t1 : Int)) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp keyInvSq
  -- The small root product exceeds `a * b * m`.
  have eW3 : ((r : Int) * (s1 : Int) * (t1 : Int)) ^ 2
      = ((a : Int) * (b : Int) + 1)
        * (((a : Int) * (m : Int) + 1) * ((b : Int) * (m : Int) + 1)) := by
    have h1 : ((r : Int) * (s1 : Int) * (t1 : Int)) ^ 2
        = (r : Int) ^ 2 * ((s1 : Int) ^ 2 * (t1 : Int) ^ 2) := by ring
    rw [h1, ← hrI, ← hs1I, ← ht1I]
  have eX : ((a : Int) * (b : Int) * (m : Int)) ^ 2
      = ((a : Int) * (b : Int))
        * (((a : Int) * (m : Int)) * ((b : Int) * (m : Int))) := by ring
  have hdiff : (0 : Int)
      < ((a : Int) * (b : Int) + 1)
        * (((a : Int) * (m : Int) + 1) * ((b : Int) * (m : Int) + 1))
        - ((a : Int) * (b : Int))
          * (((a : Int) * (m : Int)) * ((b : Int) * (m : Int))) := by
    have e : ((a : Int) * (b : Int) + 1)
          * (((a : Int) * (m : Int) + 1) * ((b : Int) * (m : Int) + 1))
        = ((a : Int) * (b : Int))
            * (((a : Int) * (m : Int)) * ((b : Int) * (m : Int)))
          + ((a : Int) * (b : Int) * ((a : Int) * (m : Int))
            + (a : Int) * (b : Int) * ((b : Int) * (m : Int))
            + ((a : Int) * (m : Int)) * ((b : Int) * (m : Int))
            + (a : Int) * (b : Int) + (a : Int) * (m : Int)
            + (b : Int) * (m : Int) + 1) := by ring
    rw [e, add_sub_cancel_left]
    positivity
  have hXsq : ((a : Int) * (b : Int) * (m : Int)) ^ 2
      < ((r : Int) * (s1 : Int) * (t1 : Int)) ^ 2 := by
    rw [eW3, eX]; linarith [hdiff]
  have hW : (a : Int) * (b : Int) * (m : Int)
      < (r : Int) * (s1 : Int) * (t1 : Int) := by
    apply jones_base_lt _ _ _ hXsq
    positivity
  have hB : (b : Int) < (c : Int) := by exact_mod_cast hbc
  have hb0 : (0 : Int) < (b : Int) := by exact_mod_cast (lt_trans ha hab)
  have hm0 : (0 : Int) < (m : Int) := by exact_mod_cast hmpos
  have hmI1 : (1 : Int) ≤ (m : Int) := by exact_mod_cast hmpos
  have hmcI : ((m : Nat) : Int) < (c : Int) := by exact_mod_cast hmc
  have hABnn : (0 : Int) ≤ 4 * ((a : Int) * (b : Int)) := by positivity
  have h4 : 4 * ((a : Int) * (b : Int)) * 1
      ≤ 4 * ((a : Int) * (b : Int)) * (m : Int) :=
    mul_le_mul_of_nonneg_left hmI1 hABnn
  rcases lt_trichotomy m a with h1 | h1 | h1
  · -- Case m < a: apply the bound to (m, a, b), max is b.
    obtain ⟨_, hm4, ha4⟩ := jones_order m a b h1 hab
    have hlt := jones_dminus_lt m a b s1 t1 r hmpos ha (lt_trans ha hab)
      hm4 ha4 (by rw [mul_comm m a]; exact hs1.symm)
      (by rw [mul_comm m b]; exact ht1.symm) hr.symm
    have hltB : (a : Int) + (b : Int) + (m : Int)
        + 2 * (a : Int) * (b : Int) * (m : Int)
        - 2 * (r : Int) * (s1 : Int) * (t1 : Int) < (b : Int) := by
      linear_combination hlt
    have hfin : 4 * ((a : Int) * (b : Int)) < (c : Int) :=
      jones_finish (a : Int) (b : Int) (c : Int) (m : Int) (r : Int) (s1 : Int) (t1 : Int)
        haI hb0 hm0 hB hmcI hor (Or.inl hltB) hW h4
    have hfin2 : (4 : Int) * (a : Int) * (b : Int) < (c : Int) := by
      linear_combination hfin
    exact_mod_cast hfin2
  · exact absurd h1 hmnea
  · rcases lt_trichotomy m b with h2 | h2 | h2
    · -- Case a < m < b: apply the bound to (a, m, b), max is b.
      obtain ⟨_, ha4, hm4b⟩ := jones_order a m b h1 h2
      have hlt := jones_dminus_lt a m b s1 r t1 ha hmpos (lt_trans ha hab)
        ha4 hm4b hs1.symm hr.symm
        (by rw [mul_comm m b]; exact ht1.symm)
      have hltB : (a : Int) + (b : Int) + (m : Int)
          + 2 * (a : Int) * (b : Int) * (m : Int)
          - 2 * (r : Int) * (s1 : Int) * (t1 : Int) < (b : Int) := by
        linear_combination hlt
      have hfin : 4 * ((a : Int) * (b : Int)) < (c : Int) :=
        jones_finish (a : Int) (b : Int) (c : Int) (m : Int) (r : Int) (s1 : Int) (t1 : Int)
          haI hb0 hm0 hB hmcI hor (Or.inl hltB) hW h4
      have hfin2 : (4 : Int) * (a : Int) * (b : Int) < (c : Int) := by
        linear_combination hfin
      exact_mod_cast hfin2
    · exact absurd h2 hmneb
    · -- Case b < m: apply the bound to (a, b, m), max is m < c.
      obtain ⟨_, ha4, hb4⟩ := jones_order a b m hab h2
      have hlt := jones_dminus_lt a b m r s1 t1 ha (lt_trans ha hab) hmpos
        ha4 hb4 hr.symm hs1.symm ht1.symm
      have hltM : (a : Int) + (b : Int) + (m : Int)
          + 2 * (a : Int) * (b : Int) * (m : Int)
          - 2 * (r : Int) * (s1 : Int) * (t1 : Int) < (m : Int) := by
        linear_combination hlt
      have hfin : 4 * ((a : Int) * (b : Int)) < (c : Int) :=
        jones_finish (a : Int) (b : Int) (c : Int) (m : Int) (r : Int) (s1 : Int) (t1 : Int)
          haI hb0 hm0 hB hmcI hor (Or.inr hltM) hW h4
      have hfin2 : (4 : Int) * (a : Int) * (b : Int) < (c : Int) := by
        linear_combination hfin
      exact_mod_cast hfin2

#print axioms solution
