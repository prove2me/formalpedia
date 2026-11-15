-- Prove2me | Theorems.Thm_BinaryQuadraticForm_kronecker_hurwitz_class_number_relation
-- name    : BinaryQuadraticForm.kronecker_hurwitz_class_number_relation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:35:49.505022+00:00
-- url     : https://prove2.me/theorems/b87b7e76-42b0-4359-afcb-5f81b504eea7
-- title:
--   The Kronecker-Hurwitz class number relation: $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$
-- statement:
--   For an integer $N > 0$ let $H(N)$ be the Hurwitz class number: the number of $\mathrm{SL}_2(\mathbb Z)$-equivalence classes of positive definite integral binary quadratic forms $ax^2 + bxy + cy^2$ of discriminant $b^2 - 4ac = -N$, primitive or not, where the class of a multiple of $x^2 + y^2$ is counted with weight $\tfrac12$ and the class of a multiple of $x^2 + xy + y^2$ with weight $\tfrac13$. Put $H(0) = -\tfrac1{12}$. Every class contains exactly one reduced form, that is, one with
--
--   $$|b| \le a \le c, \qquad b \ge 0 \text{ whenever } |b| = a \text{ or } a = c,$$
--
--   so $H(N)$ is the sum of the weights $w(a,b,c)$ of the reduced forms of discriminant $-N$, where $w(a,a,a) = \tfrac13$, $w(a,0,a) = \tfrac12$ and $w(a,b,c) = 1$ otherwise. For example $H(3) = \tfrac13$, $H(4) = \tfrac12$, $H(7) = 1$ and $H(12) = \tfrac43$.
--
--   Then for every integer $n \ge 1$
--
--   $$\sum_{\substack{t \in \mathbb Z \\ t^2 \le 4n}} H(4n - t^2) \;=\; 2\sigma(n) - \sum_{d \mid n} \min\Big(d, \frac nd\Big),$$
--
--   where $\sigma(n) = \sum_{d \mid n} d$ and $d$ runs over the positive divisors of $n$. Equivalently, the right side is $\sum_{ad = n,\ a, d > 0} \max(a, d)$. For $n = 1$: $2H(0) + 2H(3) + H(4) = -\tfrac16 + \tfrac23 + \tfrac12 = 1 = 2 \cdot 1 - 1$.
--
--   Role: this is the class number relation of Kronecker (1860) and Hurwitz (1885). It is the level-one, weight-two case of the Eichler-Selberg trace formula for the Hecke operator $T_n$ (the space of weight-two cusp forms for $\mathrm{SL}_2(\mathbb Z)$ is zero), and via Deuring's correspondence between traces of Frobenius and class numbers it counts elliptic curves over finite fields; in that form it is one of the inputs of a proof of the Ramanujan-Petersson bound in weight two.
--
--   **Formalization Note**: a form is a triple `r : ℤ × ℤ × ℤ`, with `r.1`, `r.2.1`, `r.2.2` the coefficients $a, b, c$ of $x^2$, $xy$, $y^2$; the reducedness condition is the one of the reduction theorem `BinaryQuadraticForm.existsUnique_reduced_and_finite`. For $t^2 < 4n$ the inner sum, over the triples in the box $[1, 4n] \times [-4n, 4n] \times [1, 4n]$ that are reduced of discriminant $t^2 - 4n$, is $H(4n - t^2)$: the box contains every reduced form of that discriminant, since such a form has $a \ge 1$, $|b| \le a \le c$ and $3ac \le 4n - t^2$. The term $t^2 = 4n$, present when $n$ is a square, is $H(0) = -\tfrac1{12}$. The sum over $t$ runs over $[-2n, 2n]$, which contains every $t$ with $t^2 \le 4n$. $\sigma(n)$ is written as `∑ d ∈ n.divisors, d`, and `n / d` is natural-number division, exact for $d \mid n$.
-- source:
--   L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016), Theorem 1; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib

set_option autoImplicit false

theorem BinaryQuadraticForm.kronecker_hurwitz_class_number_relation (n : ℕ) (hn : 0 < n) :
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)),
      (if t ^ 2 = 4 * (n : ℤ) then (-1 / 12 : ℚ) else
        ∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
            Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
              r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
                (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
          (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
            else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) =
      2 * ∑ d ∈ n.divisors, (d : ℚ) - ∑ d ∈ n.divisors, ((min d (n / d) : ℕ) : ℚ) := by sorry
