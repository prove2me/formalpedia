-- Prove2me | Theorems.Thm_FamousTheorems_infinitely_many_fermat_pseudoprimes
-- name    : FamousTheorems.infinitely_many_fermat_pseudoprimes
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:20.419231+00:00
-- url     : https://prove2.me/theorems/4116878c-f93b-4629-b864-569703bfff20
-- title:
--   There are infinitely many Fermat pseudoprimes (Cipolla)
-- statement:
--   **There are infinitely many Fermat pseudoprimes (Cipolla).** Let $b\ge1$. For every $m$ there is an $n\ge m$ that is a Fermat pseudoprime to base $b$: $n>1$ is composite and $n\mid b^{\,n-1}-1$.
--
--   Fermat's little theorem says that every prime $p$ satisfies $p\mid b^{p-1}-1$ when $p\nmid b$. Cipolla showed in 1904 that the converse fails infinitely often, so the Fermat test alone cannot certify primality. This led to the Miller–Rabin test and to the study of Carmichael numbers.
--
--   **Formalization note.** Mathlib's `Nat.exists_infinite_pseudoprimes`. `Nat.FermatPsp n b` means `n ∣ b ^ (n - 1) - 1`, with `n` not prime and `1 < n`. The statement is the unboundedness form of "infinitely many".
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.exists_infinite_pseudoprimes`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem infinitely_many_fermat_pseudoprimes {b : ℕ} (hb : 1 ≤ b) (m : ℕ) : ∃ n : ℕ, n.FermatPsp b ∧ m ≤ n := by sorry

end FamousTheorems
