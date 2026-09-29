-- Prove2me | Theorems.Thm_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
-- name    : DeligneSerre.eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5dba06eb-c746-50dd-a37c-860f92ef1941
-- title:
--   Finite Euler products matched by a functional equation are trivial
-- statement:
--   Let $S$ be a finite set of natural numbers, each of which is prime, let $e:\mathbb N\to\mathbb Z$, let $\omega\in\mathbb C$ be non-zero, and let $P,Q,P',Q':\mathbb N\to\mathbb C[X]$ be four families of complex polynomials such that for every $p\in S$ the polynomials $P_p,Q_p,P'_p,Q'_p$ all have constant coefficient $1$. Assume that for every $p\in S$ each root $z$ of $P_p$ and each root $z$ of $P'_p$ satisfies $1<\|z\|^2p$, and that for every $p\in S$ at least one of the following two alternatives holds: either every root $z$ of $Q_p$ and every root $z$ of $Q'_p$ satisfies $1<\|z\|^2p$; or every root of $P_p$ and every root of $P'_p$ has absolute value $1$, and moreover $\deg Q_p\le 2$ with $\|(Q_p)_2\|=1$ and $\deg Q'_p\le 2$ with $\|(Q'_p)_2\|=1$, where $(\cdot)_2$ denotes the coefficient of $X^2$. Assume finally that for some real $\sigma_0$ and all real $s\ge\sigma_0$ one has the identity $$\Bigl(\prod_{p\in S}(p^{-s})^{e_p}\Bigr)\prod_{p\in S}P'_p(p^{\,s-1})\,Q_p(p^{-s})\;=\;\omega\prod_{p\in S}P_p(p^{-s})\,Q'_p(p^{\,s-1}),$$ the outer exponentiation by $e_p\in\mathbb Z$ being the integer power of the complex number $p^{-s}$. Then for every $p\in S$ one has $e_p=0$, $P_p=Q_p$ and $P'_p=Q'_p$ as polynomials.
--
--   This is Lemme 4.9 of Deligne–Serre on finite Euler products interchanged by a functional equation, in a form sharpened at those primes where the denominator factors $Q_p,Q'_p$ are allowed to be arbitrary quadratics $1-bX+\varepsilon X^2$ with $\|\varepsilon\|=1$ (the shape of the local factor of a weight-one Hecke eigenform at a prime outside the level), with no archimedean bound imposed on $b$. It is used by [`DeligneSerre.eq_of_eulerProduct_completedLSeries_functionalEquation`](thm.html#DeligneSerre.eq_of_eulerProduct_completedLSeries_functionalEquation), the comparison of two Dirichlet series with Euler products and a common completed functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem DeligneSerre.eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℤ) (ω : ℂ) (hω : ω ≠ 0)
    (P Q P' Q' : ℕ → ℂ[X])
    (hP₀ : ∀ p ∈ S, (P p).coeff 0 = 1) (hQ₀ : ∀ p ∈ S, (Q p).coeff 0 = 1)
    (hP'₀ : ∀ p ∈ S, (P' p).coeff 0 = 1) (hQ'₀ : ∀ p ∈ S, (Q' p).coeff 0 = 1)
    (hP : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hP' : ∀ p ∈ S, ∀ z : ℂ, (P' p).IsRoot z → 1 < ‖z‖ ^ 2 * p)
    (hQ : ∀ p ∈ S,
      ((∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∧
          ∀ z : ℂ, (Q' p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1) ∧ (∀ z : ℂ, (P' p).IsRoot z → ‖z‖ = 1) ∧
          (Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1 ∧
          (Q' p).natDegree ≤ 2 ∧ ‖(Q' p).coeff 2‖ = 1))
    (σ₀ : ℝ)
    (hFE : ∀ s : ℝ, σ₀ ≤ s →
      (∏ p ∈ S, ((p : ℂ) ^ (-(s : ℂ))) ^ (e p)) *
          ∏ p ∈ S, (P' p).eval ((p : ℂ) ^ ((s : ℂ) - 1)) * (Q p).eval ((p : ℂ) ^ (-(s : ℂ))) =
        ω * ∏ p ∈ S, (P p).eval ((p : ℂ) ^ (-(s : ℂ))) * (Q' p).eval ((p : ℂ) ^ ((s : ℂ) - 1))) :
    ∀ p ∈ S, e p = 0 ∧ P p = Q p ∧ P' p = Q' p := by sorry
