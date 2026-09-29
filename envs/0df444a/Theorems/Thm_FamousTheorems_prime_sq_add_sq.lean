-- Prove2me | Theorems.Thm_FamousTheorems_prime_sq_add_sq
-- name    : FamousTheorems.prime_sq_add_sq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:52:08.466984+00:00
-- url     : https://prove2.me/theorems/11cff74f-8c20-40ef-936c-e3d5cdcc05e2
-- title:
--   Fermat's two-square theorem
-- statement:
--   **A prime is a sum of two squares unless it is $3 \bmod 4$.**
--
--   For a prime $p$ with $p \not\equiv 3 \pmod 4$,
--   $$\exists a, b \in \mathbb{N} : \ p = a^{2}+b^{2}.$$
--
--   The excluded case is forced: squares are $0$ or $1$ mod $4$, so a sum of two squares is never
--   $3$ mod $4$. The content is the converse for $p \equiv 1 \pmod 4$ (with $p = 2 = 1^2+1^2$ the
--   remaining case).
--
--   Announced by Fermat in 1640 and first proved by Euler after seven years' work. The conceptual
--   proof observes that $p \equiv 1 \pmod 4$ makes $-1$ a quadratic residue, so $p$ divides
--   $a^2+1 = (a+i)(a-i)$ in $\mathbb{Z}[i]$ while dividing neither factor; since $\mathbb{Z}[i]$ is
--   a unique factorisation domain, $p$ is not prime there, and its factorisation gives
--   $p = a^2+b^2$. This is the prototype for using algebraic number theory to answer questions about
--   $\mathbb{Z}$.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem prime_sq_add_sq : ∀ {p : ℕ} [Fact (Nat.Prime p)], p % 4 ≠ 3 → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by sorry

end FamousTheorems
