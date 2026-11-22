-- Prove2me | Theorems.Thm_Bernstein_group_law
-- name    : Bernstein.group_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:13:25.1718+00:00
-- url     : https://prove2.me/theorems/3534e6dc-f238-4aad-93cd-b5a8e7eff9c2
-- title:
--   Appendix A — E(F_{p²}) and its addition formulas
-- statement:
--   Let $p \ge 5$ be prime and $A$ an integer with $A^2 - 4$ not a square modulo $p$, and let $E(\mathbf{F}_{p^2})$ be Mathlib's group of points of $y^2 = x^3 + Ax^2 + x$ over $\mathbf{F}_{p^2}$. Then:
--   - every $(x, y) \in \mathbf{F}_{p^2}^2$ with $y^2 = x^3 + Ax^2 + x$ is a nonsingular point, so $E(\mathbf{F}_{p^2})$ is $\{\infty\} \cup \{(x, y) : y^2 = x^3 + Ax^2 + x\}$;
--   - addition is associative and commutative, and $Q + (-Q) = \infty$, so $E(\mathbf{F}_{p^2})$ is a commutative group with identity $\infty$;
--   - $-\infty = \infty$ and $-(x, y) = (x, -y)$;
--   - $\infty + \infty = \infty$, $\infty + Q = Q + \infty = Q$, and $(x, y) + (x, -y) = \infty$;
--   - if $y \neq 0$, then $(x, y) + (x, y) = (x'', \lambda(x - x'') - y)$ with $\lambda = (3x^2 + 2Ax + 1)/2y$ and $x'' = \lambda^2 - A - 2x$, and $x'' = (x^2 - 1)^2/4y^2$;
--   - if $x' \neq x$, then $(x, y) + (x', y') = (x'', \lambda(x - x'') - y)$ with $\lambda = (y' - y)/(x' - x)$ and $x'' = \lambda^2 - A - x - x'$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 20, Appendix A, the elliptic curve and its group law

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem group_law (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    (∀ x y : Fp2 p, y ^ 2 = x ^ 3 + emb p A * x ^ 2 + x → (Ecurve p A).Nonsingular x y) ∧
    (∀ P Q R : Pt p A, P + Q + R = P + (Q + R)) ∧
    (∀ P Q : Pt p A, P + Q = Q + P) ∧
    (∀ Q : Pt p A, Q + -Q = 0) ∧
    -(0 : Pt p A) = 0 ∧
    (∀ (x y : Fp2 p) (h : (Ecurve p A).Nonsingular x y),
      ∃ h₁ : (Ecurve p A).Nonsingular x (-y), -(.some x y h : Pt p A) = .some x (-y) h₁) ∧
    (0 : Pt p A) + 0 = 0 ∧
    (∀ Q : Pt p A, 0 + Q = Q ∧ Q + 0 = Q) ∧
    (∀ (x y : Fp2 p) (h : (Ecurve p A).Nonsingular x y)
      (h₁ : (Ecurve p A).Nonsingular x (-y)),
      (.some x y h : Pt p A) + .some x (-y) h₁ = 0) ∧
    (∀ (x y : Fp2 p) (h : (Ecurve p A).Nonsingular x y), y ≠ 0 →
      let l := (3 * x ^ 2 + 2 * emb p A * x + 1) / (2 * y)
      let x'' := l ^ 2 - emb p A - 2 * x
      x'' = (x ^ 2 - 1) ^ 2 / (4 * y ^ 2) ∧
      ∃ h'' : (Ecurve p A).Nonsingular x'' (l * (x - x'') - y),
        (.some x y h : Pt p A) + .some x y h = .some x'' (l * (x - x'') - y) h'') ∧
    (∀ (x y x' y' : Fp2 p) (h : (Ecurve p A).Nonsingular x y)
      (h' : (Ecurve p A).Nonsingular x' y'), x' ≠ x →
      let l := (y' - y) / (x' - x)
      let x'' := l ^ 2 - emb p A - x - x'
      ∃ h'' : (Ecurve p A).Nonsingular x'' (l * (x - x'') - y),
        (.some x y h : Pt p A) + .some x' y' h' = .some x'' (l * (x - x'') - y) h'') := by
  sorry

end Bernstein
