-- Prove2me | Theorems.Thm_FamousTheorems_lifting_the_exponent
-- name    : FamousTheorems.lifting_the_exponent
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:10.446419+00:00
-- url     : https://prove2.me/theorems/51754086-1916-427a-b203-d2f14123388e
-- title:
--   The lifting-the-exponent lemma (odd primes)
-- statement:
--   **The lifting-the-exponent lemma (odd primes).** Let $p$ be an odd prime and $x,y$ integers with $p\mid x-y$ and $p\nmid x$. Then for every $n\ge0$,
--   $$v_p(x^n-y^n)=v_p(x-y)+v_p(n).$$
--
--   The lemma computes exactly how divisible $x^n-y^n$ is by powers of $p$. It is a standard tool in olympiad number theory and in the study of orders of elements modulo prime powers. It gives, for example, the order of $1+p$ modulo $p^k$ and the structure of $(\mathbb Z/p^k)^\times$.
--
--   **Formalization note.** Mathlib's `Int.emultiplicity_pow_sub_pow`. The valuations are written with `emultiplicity`, which takes values in `ℕ∞` and is infinite exactly for the value $0$ (for example when $n=0$). The prime is a natural number cast to `ℤ` in the divisibility hypotheses, and $v_p(n)$ is computed in `ℕ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Int.emultiplicity_pow_sub_pow`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lifting_the_exponent {p : ℕ} (hp : p.Prime) (hp1 : Odd p) {x y : ℤ} (hxy : (p : ℤ) ∣ x - y) (hx : ¬(p : ℤ) ∣ x) (n : ℕ) :
    emultiplicity (p : ℤ) (x ^ n - y ^ n) = emultiplicity (p : ℤ) (x - y) + emultiplicity p n := by sorry

end FamousTheorems
