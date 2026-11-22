-- Prove2me | Theorems.Thm_Bernstein_theorem_B_1
-- name    : Bernstein.theorem_B_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:14:21.270008+00:00
-- url     : https://prove2.me/theorems/23817e70-97c9-48f1-924c-f38974fde5f9
-- title:
--   Theorem B.1 — Montgomery's x-coordinate doubling formula
-- statement:
--   Let $p \ge 5$ be prime and $A$ an integer with $A^2 - 4$ not a square modulo $p$. Let $x, z \in \mathbf{F}_p$ with $(x, z) \neq (0, 0)$, and put
--   $$x_2 = (x^2 - z^2)^2, \qquad z_2 = 4xz(x^2 + Axz + z^2).$$
--   Then $x_2 = (x - z)^2(x + z)^2$, $z_2 = ((x + z)^2 - (x - z)^2)\big((x + z)^2 + \tfrac{A - 2}{4}((x + z)^2 - (x - z)^2)\big)$, and for every $Q \in E(\mathbf{F}_{p^2})$ with $X(Q) = x/z$, the fraction $x_2/z_2$ is defined, that is $(x_2, z_2) \neq (0, 0)$, and $X(2Q) = x_2/z_2$. Here $X(\infty) = \infty$, $X(x, y) = x$, and $x/z$ is $\infty$ when $z = 0$; $\tfrac{A - 2}{4}$ is computed in $\mathbf{F}_p$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), pp. 21–22, Theorem B.1 (Montgomery doubling)

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem theorem_B_1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (x z : ZMod p) (hxz : (x, z) ≠ (0, 0)) :
    let x₂ := (x ^ 2 - z ^ 2) ^ 2
    let z₂ := 4 * x * z * (x ^ 2 + (A : ZMod p) * x * z + z ^ 2)
    x₂ = (x - z) ^ 2 * (x + z) ^ 2 ∧
    z₂ = ((x + z) ^ 2 - (x - z) ^ 2) *
      ((x + z) ^ 2 + ((A : ZMod p) - 2) / 4 * ((x + z) ^ 2 - (x - z) ^ 2)) ∧
    ∀ Q : Pt p A, X Q = frac x z → (x₂, z₂) ≠ (0, 0) ∧ X (2 • Q) = frac x₂ z₂ := by
  sorry

end Bernstein
