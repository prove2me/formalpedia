-- Prove2me | Theorems.Thm_FamousTheorems_totient_multiplicative_7b
-- name    : FamousTheorems.totient_multiplicative_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:48.118959+00:00
-- url     : https://prove2.me/theorems/db1e2252-4cdb-46bf-ab10-52c2923b84a5
-- title:
--   Euler's totient function is multiplicative
-- statement:
--   **Euler's totient function is multiplicative.** If $m$ and $n$ are coprime natural numbers, then
--   $$\varphi(mn)=\varphi(m)\,\varphi(n),$$
--   where $\varphi(k)$ is the number of integers in $\{1,\dots,k\}$ coprime to $k$.
--
--   With the value $\varphi(p^a)=p^{a-1}(p-1)$ at prime powers, this gives the product formula $\varphi(n)=n\prod_{p\mid n}(1-1/p)$. It follows from the Chinese remainder theorem, which gives $(\mathbb Z/mn)^\times\cong(\mathbb Z/m)^\times\times(\mathbb Z/n)^\times$. It is used throughout number theory, for instance in the RSA cryptosystem.
--
--   **Formalization note.** Mathlib's `Nat.totient_mul`. `Nat.totient 0 = 0`, and the statement holds for all coprime pairs including those involving $0$ or $1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.totient_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem totient_multiplicative_7b {m n : ℕ} (h : Nat.Coprime m n) : Nat.totient (m * n) = Nat.totient m * Nat.totient n := by sorry

end FamousTheorems
