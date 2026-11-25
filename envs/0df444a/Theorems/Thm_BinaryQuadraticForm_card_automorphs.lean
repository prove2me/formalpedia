-- Prove2me | Theorems.Thm_BinaryQuadraticForm_card_automorphs
-- name    : BinaryQuadraticForm.card_automorphs
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:05:55.956555+00:00
-- url     : https://prove2.me/theorems/91b6fe9c-c596-4c60-a866-47e157060723
-- title:
--   Automorphs of positive definite binary quadratic forms: the stabilizer in $\mathrm{SL}_2(\mathbb Z)$ has order 4, 6 or 2
-- statement:
--   Let $f(x,y)=ax^2+bxy+cy^2$ be an integral binary quadratic form with $a>0$ and discriminant $D=b^2-4ac<0$, so that $f$ is positive definite, and let $g=\gcd(a,b,c)$ be its content. An automorph of $f$ is a matrix $\begin{pmatrix}p&q\\r&s\end{pmatrix}\in\mathrm{SL}_2(\mathbb Z)$ with
--
--   $$f(px+qy,\;rx+sy)=f(x,y)\qquad\text{for all }x,y\in\mathbb Z.$$
--
--   Then:
--
--   1. $f$ has exactly $4$ automorphs if $D=-4g^2$, exactly $6$ if $D=-3g^2$, and exactly $2$ (namely $\pm I$) otherwise;
--   2. if $f$ is reduced, i.e. $|b|\le a\le c$ with $b\ge0$ whenever $|b|=a$ or $a=c$, then $D=-4g^2$ holds exactly when $b=0$ and $a=c$, and $D=-3g^2$ holds exactly when $a=b=c$.
--
--   So a reduced form has $4$ automorphs if it is $a(x^2+y^2)$, $6$ if it is $a(x^2+xy+y^2)$, and only $\pm I$ otherwise. For a primitive form ($g=1$) the number of automorphs is $w(D)$, the number of units of the imaginary quadratic order of discriminant $D$: $w(-4)=4$, $w(-3)=6$ and $w(D)=2$ for $D<-4$.
--
--   Role: the automorphs of $f$ are exactly the $\gamma\in\mathrm{SL}_2(\mathbb Z)$ that fix the root $\tau=(-b+\sqrt D)/(2a)$ of $f(\tau,1)=0$ in the upper half plane under $z\mapsto(pz+q)/(rz+s)$, so the exceptional orders $4$ and $6$ occur exactly on the orbits of the elliptic points $i$ and $e^{2\pi i/3}$. These orders are the weights in the Hurwitz class number $H(N)$ of the Eichler-Selberg trace formula: $H(N)$ counts the $\mathrm{SL}_2(\mathbb Z)$-classes of positive definite forms of discriminant $-N$, the class of $f$ weighted by $2$ divided by its number of automorphs, so that $H(3)=1/3$ and $H(4)=1/2$. Together with the reduction theorem (every positive definite form is equivalent to exactly one reduced form) this gives the stabilizer of every class from its reduced representative.
--
--   **Formalization Note**: the form is given by its coefficients `a b c : ℤ` with hypotheses `0 < a` and `b ^ 2 - 4 * a * c < 0`. The automorphs form the subtype of `Matrix.SpecialLinearGroup (Fin 2) ℤ` whose entries `γ 0 0`, `γ 0 1`, `γ 1 0`, `γ 1 1` $=p,q,r,s$ satisfy the identity above for all integers $x,y$, and `Nat.card` counts them; since `Nat.card` of an infinite type is $0$, the statement also asserts that the set of automorphs is finite. The content $g$ is `Int.gcd a (Int.gcd b c)` (a natural number, cast to `ℤ`). The two exceptional conditions cannot hold together ($g>0$), so the order of the `if` branches does not matter. The reducedness condition in part 2 is the one of the reduction theorem fb451f8d (`|b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b)`), assumed in addition to the standing hypotheses.
-- source:
--   C. F. Gauss, Disquisitiones Arithmeticae (1801), Section V; H. Cohen, A Course in Computational Algebraic Number Theory, Springer GTM 138 (1993), Section 5.3; F. Diamond and J. Shurman, A First Course in Modular Forms, Springer GTM 228 (2005), Chapter 2 (elliptic points of SL_2(Z))

import Mathlib

set_option autoImplicit false

theorem BinaryQuadraticForm.card_automorphs (a b c : ℤ) (ha : 0 < a)
    (hdisc : b ^ 2 - 4 * a * c < 0) :
    Nat.card {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ // ∀ x y : ℤ,
        a * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
            b * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
            c * (γ 1 0 * x + γ 1 1 * y) ^ 2 =
          a * x ^ 2 + b * x * y + c * y ^ 2} =
        (if b ^ 2 - 4 * a * c = -4 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 then 4
        else if b ^ 2 - 4 * a * c = -3 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 then 6
        else 2) ∧
      ((|b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b)) →
        ((b ^ 2 - 4 * a * c = -4 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 ↔ b = 0 ∧ a = c) ∧
          (b ^ 2 - 4 * a * c = -3 * (Int.gcd a (Int.gcd b c) : ℤ) ^ 2 ↔ a = b ∧ b = c))) := by
  sorry
