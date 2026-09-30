-- Prove2me | solution 1 for erdos_ko_rado_permutations
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:46.32166+00:00
-- url     : https://prove2.me/submissions/6e40c7da-f961-4c70-86fd-710dcf15790a

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n)
    (F : Finset (Equiv.Perm (Fin n)))
    (hint : ∀ sigma ∈ F, ∀ tau ∈ F, ∃ i : Fin n, sigma i = tau i) :
    F.card ≤ (n - 1).factorial := by
  classical
  have hnpos : 0 < n := by omega
  let : NeZero n := ⟨by omega⟩
  let shift : F × Fin n → Equiv.Perm (Fin n) :=
    fun p ↦ p.1.1.trans (Equiv.addRight p.2)
  have hinj : Function.Injective shift := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    have hab : a = b := by
      obtain ⟨i, hi⟩ := hint s.1 s.2 t.1 t.2
      have heq := Equiv.congr_fun h i
      change s.1 i + a = t.1 i + b at heq
      rw [hi] at heq
      exact add_left_cancel heq
    subst b
    have hst : s = t := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      have heq := Equiv.congr_fun h i
      change s.1 i + a = t.1 i + a at heq
      exact add_right_cancel heq
    exact Prod.ext hst rfl
  have hcard := Fintype.card_le_of_injective shift hinj
  have hmul : F.card * n ≤ n.factorial := by
    simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
      Fintype.card_perm] using hcard
  have hfac : n.factorial = (n - 1).factorial * n := by
    have h := Nat.factorial_succ (n - 1)
    simpa only [Nat.sub_add_cancel hnpos, mul_comm] using h
  rw [hfac] at hmul
  nlinarith
