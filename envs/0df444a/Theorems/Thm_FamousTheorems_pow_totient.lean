-- Prove2me | Theorems.Thm_FamousTheorems_pow_totient
-- name    : FamousTheorems.pow_totient
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:23.148625+00:00
-- url     : https://prove2.me/theorems/727478af-b94c-45f0-a971-dc11a3193be4
-- title:
--   Euler's totient theorem
-- statement:
--   **Euler's generalisation of Fermat's little theorem.**
--
--   For $\gcd(x,n) = 1$,
--   $$x^{\varphi(n)} \equiv 1 \pmod n,$$
--   where $\varphi$ is Euler's totient function.
--
--   The units mod $n$ form a group of order $\varphi(n)$, so this is Lagrange's theorem applied to
--   the element $x$: the order of $x$ divides the order of the group. Taking $n = p$ prime gives
--   $\varphi(p) = p-1$ and Fermat's little theorem $x^{p-1} \equiv 1$.
--
--   It is the arithmetic fact underlying RSA: decryption works because the exponents are inverse
--   modulo $\varphi(n)$.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem pow_totient : ∀ {x n : ℕ}, Nat.Coprime x n → x ^ n.totient ≡ 1 [MOD n] := by sorry

end FamousTheorems
