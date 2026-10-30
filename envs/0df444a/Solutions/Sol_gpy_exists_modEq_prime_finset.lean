-- Prove2me | solution 1 for gpy_exists_modEq_prime_finset
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T02:44:11.21822+00:00
-- url     : https://prove2.me/submissions/6227e8db-496e-4ffa-b041-6c29af6786dd

/- Submission file for `gpy_exists_modEq_prime_finset` (publish2 good-count batch).
Self-contained: imports Mathlib only; the coprime-prime-product lemma
is included as a supporting lemma.
   Top-level `theorem solution` in the problem's exact binder/statement
   form. No sorry tactic, no axioms beyond the standard ones, no platform
   imports. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem coprime_prime_prod_aux {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hP : ∀ q ∈ P, Nat.Prime q) (hne : ∀ q ∈ P, q ≠ p) :
    Nat.Coprime p (∏ q ∈ P, q) := by
  induction P using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact Nat.coprime_one_right p
  | insert a P ha ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hne' : ∀ q ∈ P, q ≠ p := fun q hq => hne q (Finset.mem_insert_of_mem hq)
    have hpa : Nat.Coprime p a :=
      (Nat.coprime_primes hp (hP a (Finset.mem_insert_self a P))).mpr
        ((hne a (Finset.mem_insert_self a P)).symm)
    rw [Finset.prod_insert ha]
    exact hpa.mul_right (ih hP' hne')

theorem solution {P : Finset ℕ} (a : ℕ → ℕ)
    (hP : ∀ q ∈ P, Nat.Prime q) :
    ∃ w, ∀ q ∈ P, w ≡ a q [MOD q] := by
  induction P using Finset.induction with
  | empty =>
    exact ⟨0, fun q hq => absurd hq (Finset.notMem_empty q)⟩
  | insert p P hp ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    obtain ⟨w, hw⟩ := ih hP'
    have hpprime : Nat.Prime p := hP p (Finset.mem_insert_self p P)
    have hcop : Nat.Coprime (∏ q ∈ P, q) p := by
      apply Nat.Coprime.symm
      apply coprime_prime_prod_aux hpprime hP'
      intro q hq hqp
      subst hqp
      exact hp hq
    obtain ⟨w', hw'⟩ := Nat.chineseRemainder hcop w (a p)
    refine ⟨w', ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · exact hw'.2
    · have hqdvd : q ∣ ∏ q' ∈ P, q' := Finset.dvd_prod_of_mem _ hqP
      exact (Nat.ModEq.of_dvd hqdvd hw'.1).trans (hw q hqP)
