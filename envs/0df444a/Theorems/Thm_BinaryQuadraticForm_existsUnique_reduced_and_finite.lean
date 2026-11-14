-- Prove2me | Theorems.Thm_BinaryQuadraticForm_existsUnique_reduced_and_finite
-- name    : BinaryQuadraticForm.existsUnique_reduced_and_finite
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T23:54:17.646657+00:00
-- url     : https://prove2.me/theorems/fb451f8d-6e7d-4548-bead-36fb1b7dc088
-- title:
--   Gauss-Lagrange reduction: a positive definite binary quadratic form is $\mathrm{SL}_2(\mathbb Z)$-equivalent to exactly one reduced form, and each discriminant has finitely many reduced forms
-- statement:
--   Let $f(x,y) = ax^2 + bxy + cy^2$ be an integral binary quadratic form with $a > 0$ and discriminant $D = b^2 - 4ac < 0$, so that $f$ is positive definite. Call a form $f'$ equivalent to $f$ if
--
--   $$f'(x,y) = f(px + qy,\; rx + sy) \qquad\text{for some } \begin{pmatrix} p & q \\ r & s \end{pmatrix} \in \mathrm{SL}_2(\mathbb Z),$$
--
--   and call a form $a'x^2 + b'xy + c'y^2$ reduced if
--
--   $$|b'| \le a' \le c', \qquad\text{and}\qquad b' \ge 0 \text{ whenever } |b'| = a' \text{ or } a' = c'.$$
--
--   Then:
--
--   1. $f$ is equivalent to exactly one reduced form;
--   2. there are only finitely many reduced forms of discriminant $D$.
--
--   Since equivalent forms have the same discriminant, the positive definite forms of discriminant $D$ fall into finitely many $\mathrm{SL}_2(\mathbb Z)$-classes, one for each reduced form of discriminant $D$. In particular the class number $h(D)$, the number of classes of primitive forms, is finite and equals the number of primitive reduced forms of discriminant $D$.
--
--   Role: this is the reduction theory of Lagrange (1773) and Gauss (Disquisitiones Arithmeticae, 1801). It makes class numbers of negative discriminants finite and computable. The Hurwitz class number $H(N)$ in the Eichler-Selberg trace formula for Hecke operators is the number of reduced forms of discriminant $-N$, each weighted by $2$ divided by the order of its stabilizer in $\mathrm{SL}_2(\mathbb Z)$ (so $H(3) = 1/3$ and $H(4) = 1/2$).
--
--   **Formalization Note**: a form is a triple `r : ℤ × ℤ × ℤ`, with `r.1`, `r.2.1`, `r.2.2` the coefficients $a', b', c'$ of $x^2$, $xy$, $y^2$. The matrix $\gamma \in$ `Matrix.SpecialLinearGroup (Fin 2) ℤ` has entries `γ 0 0`, `γ 0 1`, `γ 1 0`, `γ 1 1` $= p, q, r, s$, and equivalence is stated as an identity of functions on $\mathbb Z^2$, which determines the coefficients. Part 2 is stated for the discriminant of the given form; a negative integer that is not the discriminant of any form has no reduced forms at all. For $D < 0$ every reduced triple of discriminant $D$ has $a' > 0$ (if $a' = 0$ then $b' = 0$ and $D = 0$), so it is positive definite.
-- source:
--   C. F. Gauss, Disquisitiones Arithmeticae (1801), arts. 171-172; J.-L. Lagrange, Recherches d'arithmetique, Nouv. Mem. Acad. Berlin (1773); D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Section 2.A (Theorem 2.8)

import Mathlib

set_option autoImplicit false

theorem BinaryQuadraticForm.existsUnique_reduced_and_finite (a b c : ℤ) (ha : 0 < a)
    (hdisc : b ^ 2 - 4 * a * c < 0) :
    (∃! r : ℤ × ℤ × ℤ,
      (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1)) ∧
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ x y : ℤ,
        r.1 * x ^ 2 + r.2.1 * x * y + r.2.2 * y ^ 2 =
          a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            c * (γ 1 0 * x + γ 1 1 * y) ^ 2) ∧
    {r : ℤ × ℤ × ℤ | r.2.1 ^ 2 - 4 * r.1 * r.2.2 = b ^ 2 - 4 * a * c ∧
      (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))}.Finite := by sorry
