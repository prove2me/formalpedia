-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_e_values_rat_linear_independent
-- name    : EulerMascheroni.Mixed.e_values_rat_linear_independent
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-14T19:57:14.965316+00:00
-- url     : https://prove2.me/theorems/2cf40c8e-df9f-40a9-b42a-7672c29c7ab3
-- title:
--   $1$, $e$ and $e\,\mathrm{Ein}(1)$ are linearly independent over $\mathbb{Q}$
-- statement:
--   Let $\operatorname{Ein}(z)=\sum_{n\ge 1}\frac{(-1)^{n+1}z^{n}}{n\cdot n!}$ be the entire exponential integral and $A(z)=e^{z}\operatorname{Ein}(z)$; equivalently $A(z)=\sum_{k\ge1}H_k\,z^k/k!$ with $H_k$ the harmonic numbers (proved on the platform as `formal_expEin_harmonic_coefficients`). The assertion is that the three real numbers
--
--   $$1,\qquad e,\qquad A(1)=e\operatorname{Ein}(1)$$
--
--   are linearly independent over $\mathbb{Q}$: for rational numbers $a,b,c$,
--
--   $$a+b\,e+c\,e\operatorname{Ein}(1)=0\quad\Longrightarrow\quad a=b=c=0 .$$
--
--   **Status.** This is an established theorem, not a conjecture. The functions $1,\;e^{z},\;e^{z}\operatorname{Ein}(z)$ are E-functions with rational coefficients, they satisfy a first-order system $z\,y'=B(z)\,y$ with $B\in M_3(\mathbb{Q}[z])$ whose only finite singularity is $z=0$, and they are linearly independent over $\mathbb{C}(z)$ (platform theorem `formal_e_functional_independence`). Shidlovskii's First Fundamental Theorem (Siegel's method) then gives linear independence of the values at $z=1$ over $\mathbb{Q}$, indeed over $\overline{\mathbb{Q}}$.
--
--   **Why this weaker statement is worth isolating.** The algebraic-coefficient version `e_values_linear_independent` is currently reduced on the platform to Beukers' refined lifting theorem and ultimately to the André–Beukers zero-singularity theorem. The present statement asks only for *rational* coefficients and only for *this one explicit rank-three system*. Its proof needs no descent from $\overline{\mathbb{Q}}$, no number-field arithmetic, no André holomorphic-basis theorem and no zero-singularity theorem: only Siegel's original method for a single system — an integer Hermite–Padé construction (Siegel's lemma is `exists_ne_zero_int_vec_norm_le` in Mathlib), the elementary denominator arithmetic of $1/k!$ and $1/(k\cdot k!)$, the growth estimate of the remainder at $z=1$, and a non-vanishing (Shidlovskii-type) determinant argument specialised to this system.
--
--   **Role in the mission.** By the Hardy identity $e\operatorname{Ein}(1)=e\gamma+\delta$ (platform theorem `hardy_identity`), if both Euler's constant $\gamma$ and the Euler–Gompertz constant $\delta$ were rational then
--
--   $$(-\delta)+(-\gamma)\,e+1\cdot e\operatorname{Ein}(1)=0$$
--
--   would be a non-trivial rational relation. Hence this statement alone implies Aptekarev's theorem that at least one of $\gamma,\delta$ is irrational, without passing through Rivoal's transcendence disjunction. It says nothing about $\gamma$ or $\delta$ individually: every value of this E-system at $1$ involves $\gamma$ and $\delta$ only through the combination $e\gamma+\delta$.
-- source:
--   Rational-coefficient case of Shidlovskii's First Fundamental Theorem (Siegel's method) for the E-function system (1, e^z, e^z Ein(z)): A. B. Shidlovskii, Transcendental Numbers, de Gruyter Studies in Math. 12, 1989, Chapter 3 (First Fundamental Theorem); C. L. Siegel, Über einige Anwendungen diophantischer Approximationen, Abh. Preuss. Akad. Wiss. 1929, Teil I. Application to this system and the identity e Ein(1) = e gamma + delta: T. Rivoal, On the arithmetic nature of the values of the gamma function, Euler's constant, and Gompertz's constant, Michigan Math. J. 61 (2012), Section 1 (proof of Theorem 1). Consequence: A. I. Aptekarev (ed.), Rational approximants for Euler's constant and recurrence relations, Sovrem. Probl. Mat. 9 (2007), main theorem (at least one of gamma, delta is irrational).

import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Mixed.e_values_rat_linear_independent
    (a b c : ℚ)
    (h : (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by sorry
