-- Prove2me | Theorems.Thm_Bernstein_eq_zero_of_cubic_eq_zero
-- name    : Bernstein.eq_zero_of_cubic_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:14:01.898481+00:00
-- url     : https://prove2.me/theorems/bc4a3803-444d-4a25-99f1-35968879e27f
-- title:
--   Appendix A — x³ + Ax² + x = 0 in F_p forces x = 0
-- statement:
--   Let $p \ge 5$ be prime and $A$ an integer with $A^2 - 4$ not a square modulo $p$. If $x \in \mathbf{F}_p$ and $x^3 + Ax^2 + x = 0$, then $x = 0$. Equivalently, for $x \in \mathbf{F}_p$ with $x \neq 0$, the point $(x, 0)$ does not satisfy $y^2 = x^3 + Ax^2 + x$ over $\mathbf{F}_{p^2}$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 20, Appendix A, no point (x, 0) with x ≠ 0

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem eq_zero_of_cubic_eq_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    (∀ x : ZMod p, x ^ 3 + (A : ZMod p) * x ^ 2 + x = 0 → x = 0) ∧
    (∀ x : ZMod p, x ≠ 0 → ¬ (Ecurve p A).Equation (emb p x) 0) := by
  sorry

end Bernstein
