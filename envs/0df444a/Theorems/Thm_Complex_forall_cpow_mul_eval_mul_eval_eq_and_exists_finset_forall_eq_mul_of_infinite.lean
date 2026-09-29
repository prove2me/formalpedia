-- Prove2me | Theorems.Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
-- name    : Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/1b2ff38a-4b19-536e-8bdc-975f7432d234
-- title:
--   Laurent identity in q^{-s} and cancellation of the denominator
-- statement:
--   Let $q$ be a natural number with $q>1$, let $P,Q_1,Q_2\in\mathbb{C}[X]$ with $Q_2\neq 0$, let $m,k\in\mathbb{Z}$, let $\gamma,Z^\vee\colon\mathbb{C}\to\mathbb{C}$ be arbitrary functions, and let $S,S_1\subseteq\mathbb{C}$ be sets, where the set of real $t$ with $t\in S$ (via the inclusion $\mathbb{R}\hookrightarrow\mathbb{C}$) is infinite, while no condition is imposed on $S_1$. Assume that $q^{ms}P(q^{-s})Q_2(q^{-s})=Q_1(q^{-s})q^{ks}$ for all $s\in S$, and that $Z^\vee(s)Q_2(q^{-s})=Q_1(q^{-s})q^{ks}\gamma(s)$ for all $s\in S_1$, all complex powers being the principal ones of the natural number $q$. The conclusion is the conjunction of two assertions: first, the identity $q^{ms}P(q^{-s})Q_2(q^{-s})=Q_1(q^{-s})q^{ks}$ holds for every $s\in\mathbb{C}$, not merely on $S$; second, there exists a finite set $R\subseteq\mathbb{R}$ such that for every $s\in S_1$ with $q^{-\operatorname{Re}s}\notin R$ one has $Z^\vee(s)=\gamma(s)\bigl(q^{ms}P(q^{-s})\bigr)$.
--
--   This is the elementary step by which a rational local functional equation with a point-dependent denominator $Q_2(q^{-s})$ is converted into an unconditional identity of Laurent polynomials in $q^{-s}$ and then transported to the dual side away from finitely many vertical lines. It is used in the construction of the local Rankin–Selberg zeta integrals and their local functional equations for $\mathrm{GL}(3)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
    (q : ℕ) (hq : 1 < q) (P Q₁ Q₂ : Polynomial ℂ) (hQ₂ : Q₂ ≠ 0) (m k : ℤ) (γ Zd : ℂ → ℂ) (S S₁ : Set ℂ)
    (hS : {t : ℝ | (t : ℂ) ∈ S}.Infinite)
    (h : ∀ s ∈ S,
      (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s))
    (h₁ : ∀ s ∈ S₁,
      Zd s * Q₂.eval ((q : ℂ) ^ (-s)) = Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) * γ s) :
    (∀ s : ℂ, (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)) * Q₂.eval ((q : ℂ) ^ (-s)) =
        Q₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s)) ∧
    ∃ R : Finset ℝ, ∀ s ∈ S₁, (q : ℝ) ^ (-s.re) ∉ R →
      Zd s = γ s * ((q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s))) := by sorry
