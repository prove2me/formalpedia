-- Prove2me | Theorems.Thm_FamousTheorems_goldbach_fermat_numbers_coprime
-- name    : FamousTheorems.goldbach_fermat_numbers_coprime
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:09.458754+00:00
-- url     : https://prove2.me/theorems/91029364-808e-41db-aebf-ed6867d829d8
-- title:
--   Goldbach's theorem on Fermat numbers
-- statement:
--   **Goldbach's theorem on Fermat numbers.** Distinct Fermat numbers $F_n=2^{2^n}+1$ are pairwise coprime.
--
--   Goldbach noted this in a 1730 letter to Euler. The proof uses the identity $F_0F_1\cdots F_{n-1}=F_n-2$, so any common divisor of $F_m$ and $F_n$ divides $2$, and Fermat numbers are odd. Since each Fermat number has a prime factor not shared by any other, this gives another proof that there are infinitely many primes.
--
--   **Formalization note.** Mathlib's `Nat.coprime_fermatNumber_fermatNumber`. `Nat.fermatNumber n` is $2^{2^n}+1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.coprime_fermatNumber_fermatNumber`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem goldbach_fermat_numbers_coprime {m n : ℕ} (h : m ≠ n) :
    Nat.Coprime (Nat.fermatNumber m) (Nat.fermatNumber n) := by sorry

end FamousTheorems
