-- Prove2me | Theorems.Thm_Bernstein_theorem_B_2
-- name    : Bernstein.theorem_B_2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:14:44.234029+00:00
-- url     : https://prove2.me/theorems/a78e19ac-ab49-4536-a85c-68ee143a157d
-- title:
--   Theorem B.2 — Montgomery's x-coordinate differential addition formula
-- statement:
--   Let $p \ge 5$ be prime and $A$ an integer with $A^2 - 4$ not a square modulo $p$. Let $x, z, x', z', x_1, z_1 \in \mathbf{F}_p$ with $(x, z) \neq (0, 0)$, $(x', z') \neq (0, 0)$, $x_1 \neq 0$ and $z_1 \neq 0$, and put
--   $$x_3 = 4(xx' - zz')^2 z_1, \qquad z_3 = 4(xz' - zx')^2 x_1.$$
--   Then $x_3 = ((x - z)(x' + z') + (x + z)(x' - z'))^2 z_1$, $z_3 = ((x - z)(x' + z') - (x + z)(x' - z'))^2 x_1$, and for all $Q, Q' \in E(\mathbf{F}_{p^2})$ with $X(Q) = x/z$, $X(Q') = x'/z'$ and $X(Q - Q') = x_1/z_1$, the fraction $x_3/z_3$ is defined, that is $(x_3, z_3) \neq (0, 0)$, and $X(Q + Q') = x_3/z_3$. Here $X(\infty) = \infty$, $X(x, y) = x$, and $x/z$ is $\infty$ when $z = 0$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 22, Theorem B.2 (Montgomery differential addition)

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem theorem_B_2 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (x z x' z' x₁ z₁ : ZMod p)
    (hxz : (x, z) ≠ (0, 0)) (hxz' : (x', z') ≠ (0, 0)) (hx₁ : x₁ ≠ 0) (hz₁ : z₁ ≠ 0) :
    let x₃ := 4 * (x * x' - z * z') ^ 2 * z₁
    let z₃ := 4 * (x * z' - z * x') ^ 2 * x₁
    x₃ = ((x - z) * (x' + z') + (x + z) * (x' - z')) ^ 2 * z₁ ∧
    z₃ = ((x - z) * (x' + z') - (x + z) * (x' - z')) ^ 2 * x₁ ∧
    ∀ Q Q' : Pt p A, X Q = frac x z → X Q' = frac x' z' → X (Q - Q') = frac x₁ z₁ →
      (x₃, z₃) ≠ (0, 0) ∧ X (Q + Q') = frac x₃ z₃ := by
  sorry

end Bernstein
