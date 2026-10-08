-- Prove2me | solution 1 for no_bad_primes_two_squares
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:51:42.713783+00:00
-- url     : https://prove2.me/submissions/080ee2a3-3321-4940-8565-2f784692ab70

import Mathlib

/-!
**Fermat's two-squares theorem (backward direction)**: if every prime factor of `n`
is not congruent to 3 mod 4, then `n` is a sum of two squares.

Follows from: primes `p` with `p % 4 ≠ 3` are sums of two squares (Mathlib:
`Nat.Prime.sq_add_sq`), and the Brahmagupta–Fibonacci identity: products of sums of
two squares are sums of two squares (Mathlib: `Nat.sq_add_sq_mul`). The proof is by
strong induction on `n`, extracting one prime factor at a time.
-/

open Nat

theorem solution (n : ℕ) (hn : ∀ p ∈ n.primeFactors, p % 4 ≠ 3) :
    ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with (_ | _ | m)
    · exact ⟨0, 0, rfl⟩
    · exact ⟨1, 0, rfl⟩
    · -- n = m + 2 > 1; extract a prime factor via minFac
      have hgt : m + 2 ≠ 1 := by omega
      have hpp : (m + 2).minFac.Prime := (m + 2).minFac_prime hgt
      have hdvd : (m + 2).minFac ∣ (m + 2) := (m + 2).minFac_dvd
      haveI : Fact (m + 2).minFac.Prime := ⟨hpp⟩
      have hp_mem : (m + 2).minFac ∈ (m + 2).primeFactors :=
        mem_primeFactors.mpr ⟨hpp, hdvd, by omega⟩
      have hp4 : (m + 2).minFac % 4 ≠ 3 := hn _ hp_mem
      -- p = minFac is a sum of two squares
      obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq hp4
      -- Factor: m + 2 = minFac * w
      obtain ⟨w, hw⟩ := hdvd
      -- w < m + 2
      have hwlt : w < m + 2 := by
        by_contra hge
        push_neg at hge
        rw [hw] at hge
        have hple : 2 ≤ (m + 2).minFac := hpp.two_le
        nlinarith
      -- w inherits the hypothesis
      have hwp : ∀ q ∈ w.primeFactors, q % 4 ≠ 3 := by
        intro q hq
        refine hn q ?_
        have hqprime := Nat.prime_of_mem_primeFactors hq
        have hqdvd_w : q ∣ w := Nat.dvd_of_mem_primeFactors hq
        have hqdvd : q ∣ (m + 2) := by
          rw [hw]
          exact hqdvd_w.mul_left _
        exact mem_primeFactors.mpr ⟨hqprime, hqdvd, by omega⟩
      -- Apply IH to w
      obtain ⟨x, y, hxy⟩ := ih w hwlt hwp
      -- Combine via Brahmagupta-Fibonacci
      obtain ⟨r, s, hrs⟩ := Nat.sq_add_sq_mul huv.symm hxy
      exact ⟨r, s, by rw [hw]; exact hrs⟩
