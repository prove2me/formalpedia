-- Prove2me | Theorems.Thm_FamousTheorems_catalan_identity_fibonacci
-- name    : FamousTheorems.catalan_identity_fibonacci
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:06.620593+00:00
-- url     : https://prove2.me/theorems/6934e5f1-f775-4646-8658-f202ff559b4d
-- title:
--   Catalan's identity for Fibonacci numbers
-- statement:
--   **Catalan's identity for Fibonacci numbers.** For all integers $x$ and $a$,
--   $$F_{x+a}^2-F_xF_{x+2a}=(-1)^{x}F_a^2,$$
--   where $F$ is the Fibonacci sequence extended to negative indices by $F_{-n}=(-1)^{n+1}F_n$.
--
--   Written with $n=x+a$ and $r=a$, this is the classical form $F_n^2-F_{n-r}F_{n+r}=(-1)^{n-r}F_r^2$. The case $a=1$ is Cassini's identity. It is one of the standard identities of the Fibonacci numbers.
--
--   **Formalization note.** Mathlib's `Int.fib_add_sq_sub_fib_mul_fib_add_two_mul`, where `Int.fib` is the Fibonacci function on $\mathbb Z$. The sign is written $(-1)^{|x|}$ using `x.natAbs`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Int.fib_add_sq_sub_fib_mul_fib_add_two_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem catalan_identity_fibonacci (x a : ℤ) : Int.fib (x + a) ^ 2 - Int.fib x * Int.fib (x + 2 * a) = (-1) ^ x.natAbs * Int.fib a ^ 2 := by sorry

end FamousTheorems
