-- Prove2me | solution 1 for diophantine_descent_step_exists
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T05:36:31.290796+00:00
-- url     : https://prove2.me/submissions/8da17149-f211-4741-89d0-7769d26298aa

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ByContra
import Mathlib.Data.Int.Basic
import Definitions.Def_diophantine_descent

set_option autoImplicit false

open DiophantineDescent

/-- Auxiliary: `a^2 + 1` is never a square for `1 ≤ a`. -/
theorem aux_nonsq_succ (a : Nat) (ha : 1 ≤ a) : ¬ ∃ k : Nat, a ^ 2 + 1 = k ^ 2 := by
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

theorem solution (a b c : Nat) (h : Triple a b c)
    (hne : ¬ Euler a b c) :
    ∃ x y z : Nat, Step a b c x y z := by
  have hTri : Triple a b c := h
  obtain ⟨ha, hab, hbc, ⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ := h
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
  have hma : ∃ k : Nat, m * a + 1 = k ^ 2 := by
    obtain ⟨k, hk⟩ := ham
    exact ⟨k, by rw [mul_comm]; exact hk⟩
  have hmb : ∃ k : Nat, m * b + 1 = k ^ 2 := by
    obtain ⟨k, hk⟩ := hbm
    exact ⟨k, by rw [mul_comm]; exact hk⟩
  have hmnea : m ≠ a := by
    intro heq
    obtain ⟨k, hk⟩ := ham
    have hkk : a * a + 1 = k ^ 2 := heq ▸ hk
    have hsq : a ^ 2 + 1 = k ^ 2 := by
      calc a ^ 2 + 1 = a * a + 1 := by ring
        _ = k ^ 2 := hkk
    exact aux_nonsq_succ a (by omega) ⟨k, hsq⟩
  have hmneb : m ≠ b := by
    intro heq
    obtain ⟨k, hk⟩ := hbm
    have hkk : b * b + 1 = k ^ 2 := heq ▸ hk
    have hsq : b ^ 2 + 1 = k ^ 2 := by
      calc b ^ 2 + 1 = b * b + 1 := by ring
        _ = k ^ 2 := hkk
    exact aux_nonsq_succ b (by omega) ⟨k, hsq⟩
  rcases lt_trichotomy m a with hma_lt | hma_eq | hma_gt
  · refine ⟨m, a, b, ?_⟩
    refine ⟨hTri, hne, ⟨hmpos, by omega, by omega, ?_, ?_, ?_⟩,
      ⟨r, s, t, m, hr, hs, ht, hm', hmpos, hmc, ?_⟩⟩
    · exact hma
    · exact hmb
    · exact ⟨r, hr⟩
    · have p1 : ([m, a, b] : List Nat).Perm [a, m, b] := List.Perm.swap a m [b]
      have p2 : ([a, m, b] : List Nat).Perm [a, b, m] :=
        List.Perm.cons a (List.Perm.swap b m [])
      exact p1.trans p2
  · exact absurd hma_eq hmnea
  · rcases lt_trichotomy m b with hmb_lt | hmb_eq | hmb_gt
    · refine ⟨a, m, b, ?_⟩
      refine ⟨hTri, hne, ⟨ha, by omega, by omega, ham, ⟨r, hr⟩, hmb⟩,
        ⟨r, s, t, m, hr, hs, ht, hm', hmpos, hmc, ?_⟩⟩
      exact (List.Perm.cons a) (List.Perm.swap b m [])
    · exact absurd hmb_eq hmneb
    · refine ⟨a, b, m, ?_⟩
      refine ⟨hTri, hne, ⟨ha, hab, by omega, ⟨r, hr⟩, ham, hbm⟩,
        ⟨r, s, t, m, hr, hs, ht, hm', hmpos, hmc, ?_⟩⟩
      exact List.Perm.rfl

#print axioms solution
