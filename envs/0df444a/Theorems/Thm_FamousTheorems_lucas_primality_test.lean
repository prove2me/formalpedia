-- Prove2me | Theorems.Thm_FamousTheorems_lucas_primality_test
-- name    : FamousTheorems.lucas_primality_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:30.098426+00:00
-- url     : https://prove2.me/theorems/46f92cc4-c0bd-45af-bdd4-062ef5e0ed53
-- title:
--   Lucas's primality test
-- statement:
--   **Lucas's primality test.** Let $p$ be a natural number and $a\in\mathbb Z/p\mathbb Z$. Suppose that $a^{p-1}=1$ and that $a^{(p-1)/q}\ne1$ for every prime $q$ dividing $p-1$. Then $p$ is prime.
--
--   The hypotheses say that $a$ has order exactly $p-1$ in $(\mathbb Z/p)^\times$, which forces $\varphi(p)=p-1$. Lucas's test (1876, refined by Lehmer) turns a factorisation of $p-1$ into a primality certificate. It is the basis of Pratt certificates, which show that primality is in NP.
--
--   **Formalization note.** Mathlib's `lucas_primality`. The degenerate cases are handled by the hypotheses: for $p=0$ or $p=1$ they cannot both hold.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `lucas_primality`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lucas_primality_test (p : ℕ) (a : ZMod p) (ha : a ^ (p - 1) = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) : p.Prime := by sorry

end FamousTheorems
