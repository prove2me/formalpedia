-- Prove2me | solution 1 for syracuse_descent_three_mod_four_2687463_to_2787459
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:45:34.839095+00:00
-- url     : https://prove2.me/submissions/847c4b46-fcd9-49e0-8f12-3f0377c009d4

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

namespace S214SY3

def stripF : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => bif Nat.beq (x % 2) 0 then stripF f (x / 2) else x

lemma stripF_spec (f x : ℕ) (hx : x ≠ 0) (hodd : stripF f x % 2 = 1) :
    stripF f x = ordCompl[2] x := by
  induction f generalizing x with
  | zero =>
    simp only [stripF] at hodd ⊢
    symm
    apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd x Nat.prime_two).mpr
    right; omega
  | succ f ih =>
    by_cases h : x % 2 = 0
    · have hb : Nat.beq (x % 2) 0 = true := by rw [h]; rfl
      simp only [stripF, hb, cond_true] at hodd ⊢
      rw [ih (x / 2) (by omega) hodd]
      exact Nat.ordCompl_div_of_dvd Nat.prime_two (Nat.dvd_of_mod_eq_zero h)
    · have hb : Nat.beq (x % 2) 0 = false := by
        cases h' : Nat.beq (x % 2) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') h
      simp only [stripF, hb, cond_false] at hodd ⊢
      symm
      apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd x Nat.prime_two).mpr
      right; omega

def scan (start : ℕ) : ℕ → ℕ → Bool
  | 0, cur => Nat.blt cur start
  | fuel + 1, cur =>
      bif Nat.blt cur start then true
      else
        let y := stripF 64 (3 * cur + 1)
        bif Nat.beq (y % 2) 1 then scan start fuel y else false

lemma scan_sound (start fuel cur : ℕ) (h : scan start fuel cur = true) :
    ∃ t : ℕ, syracuseStep^[t] cur < start := by
  induction fuel generalizing cur with
  | zero =>
    simp only [scan, Nat.blt_eq] at h
    exact ⟨0, h⟩
  | succ fuel ih =>
    by_cases hc : cur < start
    · exact ⟨0, hc⟩
    · have hb : Nat.blt cur start = false := by
        cases h' : Nat.blt cur start
        · rfl
        · exact absurd (Nat.blt_eq.mp h') hc
      simp only [scan, hb, cond_false] at h
      cases hy : Nat.beq (stripF 64 (3 * cur + 1) % 2) 1 with
      | false => simp [hy] at h
      | true =>
        simp only [hy, cond_true] at h
        have hodd : stripF 64 (3 * cur + 1) % 2 = 1 := by simpa using hy
        have hs : stripF 64 (3 * cur + 1) = syracuseStep cur :=
          stripF_spec 64 _ (by omega) hodd
        obtain ⟨t, ht⟩ := ih _ h
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply, ← hs]
        exact ht

def chkRange (fuel : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | count + 1, a => scan a fuel a && chkRange fuel count (a + 4)

lemma chkRange_sound (fuel count a : ℕ) (h : chkRange fuel count a = true) :
    ∀ j < count, ∃ t : ℕ, syracuseStep^[t] (a + 4 * j) < a + 4 * j := by
  induction count generalizing a with
  | zero => intro j hj; omega
  | succ count ih =>
    simp only [chkRange, Bool.and_eq_true] at h
    intro j hj
    rcases j with _ | j
    · simpa using scan_sound _ _ _ h.1
    · have := ih (a + 4) h.2 j (by omega)
      rwa [show a + 4 + 4 * j = a + 4 * (j + 1) by ring] at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0 : chkRange 1024 5000 (2687463) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1 : chkRange 1024 5000 (2707463) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2 : chkRange 1024 5000 (2727463) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3 : chkRange 1024 5000 (2747463) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4 : chkRange 1024 5000 (2767463) = true := by decide +kernel

lemma big_check (c : ℕ) (hc : c < 5) : chkRange 1024 5000 (2687463 + 20000 * c) = true := by
  interval_cases c
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4

end S214SY3

open S214SY3 in
theorem solution (j : ℕ) (hj : j < 25000) :
    ∃ t : ℕ, syracuseStep^[t] (2687463 + 4 * j) < 2687463 + 4 * j := by
  have hw : 2687463 + 4 * j = 2687463 + 20000 * (j / 5000) + 4 * (j % 5000) := by omega
  have := chkRange_sound 1024 5000 _ (big_check (j / 5000) (by omega)) (j % 5000)
    (Nat.mod_lt _ (by norm_num))
  rw [← hw] at this
  exact this
