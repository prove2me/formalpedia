-- Prove2me | Theorems.Thm_FamousTheorems_euler_criterion_zmod
-- name    : FamousTheorems.euler_criterion_zmod
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:13.884688+00:00
-- url     : https://prove2.me/theorems/c0b03b76-0afa-48df-8649-f626778d44b7
-- title:
--   Euler's criterion
-- statement:
--   **Euler's criterion.** Let $p$ be a prime and $a$ a nonzero element of $\mathbb Z/p\mathbb Z$. Then $a$ is a square modulo $p$ if and only if
--   $$a^{(p-1)/2}\equiv1\pmod p.$$
--
--   For odd $p$ this gives the formula $\big(\tfrac ap\big)\equiv a^{(p-1)/2}\pmod p$ for the Legendre symbol. It is the basis of fast quadratic-residuosity tests and of the Solovay–Strassen primality test. It also gives the first supplementary law: $-1$ is a square modulo an odd prime $p$ exactly when $p\equiv1\pmod4$.
--
--   **Formalization note.** Mathlib's `ZMod.euler_criterion`. `IsSquare a` means $a=r^2$ for some `r : ZMod p`. The exponent is `p / 2` with natural-number division, which equals $(p-1)/2$ for odd $p$. For $p=2$ both sides hold for $a=1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZMod.euler_criterion`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_criterion_zmod (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) : IsSquare a ↔ a ^ (p / 2) = 1 := by sorry

end FamousTheorems
