-- Prove2me | Theorems.Thm_ECDLP_pohlig_hellman
-- name    : ECDLP.pohlig_hellman
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T23:45:11.579751+00:00
-- url     : https://prove2.me/theorems/6d8665c4-e8ea-4903-b13a-c66d11913070
-- title:
--   Pohlig–Hellman reduction to prime-power-order subgroups
-- statement:
--   Let $G$ be an additive commutative group, $P \in G$ an element of finite order $n > 0$, and $Q = xP$ for some natural number $x$. Let $m$ be a positive divisor of $n$. Then the **Pohlig–Hellman projection** satisfies:
--
--   1. the point $P' = (n/m)P$ has order exactly $m$;
--   2. the projected target satisfies $(n/m)Q = (x \bmod m)\, P'$.
--
--   Thus the discrete logarithm of $Q$ to the base $P$, reduced modulo $m$, is the discrete logarithm of $(n/m)Q$ to the base $(n/m)P$ in the subgroup of order $m$. Taking $m$ to run over the prime-power factors of $n$ and recombining by the Chinese remainder theorem is the Pohlig–Hellman algorithm (1978); when $n$ is prime, as in the challenge instance, the reduction is trivial.
--
--   **Formalization Note.** `n / m` and `x % m` are natural-number division and remainder; `•` is additive scalar multiplication. The hypothesis `0 < n` excludes the infinite-order case, where the statement would be false.
-- source:
--   Pohlig, Hellman, An improved algorithm for computing logarithms over GF(p) and its cryptographic significance, IEEE Trans. Inform. Theory 24(1) (1978), 106–110, https://doi.org/10.1109/TIT.1978.1055817; Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., 2008, §5.2.3.

import Mathlib

namespace ECDLP

theorem pohlig_hellman {G : Type*} [AddCommGroup G] {P Q : G} {n : ℕ} (hn : 0 < n)
    (hP : addOrderOf P = n) {x : ℕ} (hQ : Q = x • P) {m : ℕ} (hm : m ∣ n) :
    addOrderOf ((n / m) • P) = m ∧ (n / m) • Q = (x % m) • ((n / m) • P) := by sorry

end ECDLP
