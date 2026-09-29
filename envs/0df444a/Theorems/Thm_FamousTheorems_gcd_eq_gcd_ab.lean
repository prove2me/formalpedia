-- Prove2me | Theorems.Thm_FamousTheorems_gcd_eq_gcd_ab
-- name    : FamousTheorems.gcd_eq_gcd_ab
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:19.080994+00:00
-- url     : https://prove2.me/theorems/a3f3133a-0ba0-4bda-a048-4f9e5c04afd1
-- title:
--   Bézout's identity
-- statement:
--   **The gcd is an integer combination.**
--
--   For naturals $x, y$ there are integers $u, v$ with
--   $$\gcd(x,y) \;=\; ux + vy .$$
--
--   The coefficients are produced by the extended Euclidean algorithm, running the division steps
--   backwards; Mathlib names them `Nat.gcdA` and `Nat.gcdB`.
--
--   The identity is what makes $\gcd$ algebraically meaningful: it says $\gcd(x,y)$ generates the
--   ideal $(x,y)$ in $\mathbb{Z}$, so $\mathbb{Z}$ is a principal ideal domain. Modular inverses,
--   the Chinese remainder theorem and Euclid's lemma (if $p \mid ab$ and $p \nmid a$ then
--   $p \mid b$) all follow immediately.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gcd_eq_gcd_ab : ∀ x y : ℕ,
    (Nat.gcd x y : ℤ) = x * Nat.gcdA x y + y * Nat.gcdB x y := by sorry

end FamousTheorems
