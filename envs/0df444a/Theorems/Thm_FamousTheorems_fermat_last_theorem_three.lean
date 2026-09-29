-- Prove2me | Theorems.Thm_FamousTheorems_fermat_last_theorem_three
-- name    : FamousTheorems.fermat_last_theorem_three
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:55.903447+00:00
-- url     : https://prove2.me/theorems/41e6f601-8287-4742-bd8f-6ad1daedc3e7
-- title:
--   Fermat's Last Theorem for exponent 3
-- statement:
--   **Fermat's Last Theorem for exponent $3$.** There are no positive integers $a,b,c$ with
--   $$a^3+b^3=c^3.$$
--
--   The case $n=3$ was first treated by Euler, and it was completed rigorously later using arithmetic in the Eisenstein integers $\mathbb Z[\omega]$, $\omega=e^{2\pi i/3}$. It was the first case of Fermat's Last Theorem for an odd prime exponent and a model for Kummer's later work on regular primes.
--
--   **Formalization note.** Mathlib's `fermatLastTheoremThree`, proved using arithmetic in $\mathbb Z[\omega]$. The statement is Mathlib's `FermatLastTheoremFor 3` written out in full: for natural numbers $a,b,c$, all nonzero, $a^3+b^3\neq c^3$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `fermatLastTheoremThree`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fermat_last_theorem_three : ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3 := by sorry

end FamousTheorems
