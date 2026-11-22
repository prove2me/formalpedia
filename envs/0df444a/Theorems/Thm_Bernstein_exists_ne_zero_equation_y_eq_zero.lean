-- Prove2me | Theorems.Thm_Bernstein_exists_ne_zero_equation_y_eq_zero
-- name    : Bernstein.exists_ne_zero_equation_y_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:23:12.223779+00:00
-- url     : https://prove2.me/theorems/dca8a47c-ebb4-449c-a8e9-38bffcfa6359
-- title:
--   Bernstein, p. 20 — a point (x, 0) with x ≠ 0 exists over F_{p²}
-- statement:
--   Let $p \ge 5$ be prime and $A$ an integer such that $A^2 - 4$ is not a square modulo $p$. Then there is a nonzero $x \in \mathbf{F}_{p^2}$ (Mathlib's `GaloisField p 2`) such that $(x, 0)$ satisfies $y^2 = x^3 + Ax^2 + x$, that is, $x^3 + Ax^2 + x = 0$.
--
--   This refutes, for $x \in \mathbf{F}_{p^2}$, the sentence of D. J. Bernstein, *Curve25519: new Diffie-Hellman speed records* (2006), Appendix A, p. 20: “In other words, $(x, 0) \notin E(\mathbf{F}_{p^2})$ if $x \neq 0$.” The sentence before it, “if $x^3 + Ax^2 + x = 0$ in $\mathbf{F}_p$ then $x = 0$”, concerns $x \in \mathbf{F}_p$, and the mission states the sentence in that setting. Over $\mathbf{F}_{p^2}$, every element of $\mathbf{F}_p$ is a square, so $A^2 - 4 = r^2$ for some $r$, and $x = (-A + r)/2$ is a root of $x^2 + Ax + 1$, nonzero because the product of the two roots is $1$. The curve `Ecurve p A` is that of the mission's bundle `Curve25519Bernstein`.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 20, Appendix A, the sentence "(x, 0) ∉ E(F_{p²}) if x ≠ 0", refuted for x ∈ F_{p²} (counterexample, not in the paper)

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem exists_ne_zero_equation_y_eq_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    ∃ x : Fp2 p, x ≠ 0 ∧ (Ecurve p A).Equation x 0 := by
  sorry

end Bernstein
