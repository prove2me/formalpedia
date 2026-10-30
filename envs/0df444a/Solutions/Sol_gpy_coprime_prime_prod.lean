-- Prove2me | solution 1 for gpy_coprime_prime_prod
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T02:41:05.19645+00:00
-- url     : https://prove2.me/submissions/cfee35ee-7544-4442-91de-6204efcd4f18

/- Submission file for `gpy_coprime_prime_prod` (publish2 good-count batch).
Self-contained: imports Mathlib only.
   Top-level `theorem solution` in the problem's exact binder/statement
   form. No sorry tactic, no axioms beyond the standard ones, no platform
   imports. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
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
