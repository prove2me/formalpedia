-- Prove2me | Theorems.Thm_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation
-- name    : DeligneSerre.eq_of_eulerProduct_completedLSeries_functionalEquation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/c8b3b0df-de7a-54b8-ab3d-fe718dd049af
-- title:
--   Deligne–Serre comparison of Euler products and conductors
-- statement:
--   Let $S$ be a finite set of natural numbers, all prime, and let $a,b:\mathbb N\to\mathbb C$ satisfy $a(1)=b(1)=1$ and $a(mn)=a(m)a(n)$, $b(mn)=b(m)b(n)$ for coprime $m,n$. Let $P,Q$ assign to each natural number a polynomial over $\mathbb C$ such that for every prime $p$ the power series $P_p$ is inverse to $\sum_{k}a(p^k)X^k$ and $Q_p$ inverse to $\sum_k b(p^k)X^k$, and such that $P_p=Q_p$ for every prime $p\notin S$. Assume for $p\in S$ that every root $z$ of $P_p$ has $\|z\|=1$, and that either every root $z$ of $Q_p$ satisfies $1<\|z\|^2p$, or $\deg Q_p\le 2$ and the coefficient of $X^2$ in $Q_p$ has absolute value $1$. Let $M_a,M_b$ be non-zero naturals every prime divisor of whose product lies in $S$. Let $G:\mathbb C\to\mathbb C$, $\sigma_1\in\mathbb R$ be such that $G(s)\ne 0$ and both $L$-series $\sum a(m)m^{-s}$, $\sum b(m)m^{-s}$ converge absolutely for real $s>\sigma_1$. Let $w_a,w_b$ be non-zero and let $\Lambda_a^{(1)},\Lambda_a^{(2)},\Lambda_a'^{(1)},\Lambda_a'^{(2)}$ and $\Lambda_b^{(1)},\Lambda_b^{(2)},\Lambda_b'^{(1)},\Lambda_b'^{(2)}$ be entire, with, for real $s>\sigma_1$, $\Lambda_a^{(2)}(s),\Lambda_a'^{(2)}(s)$ non-zero, $\Lambda_a^{(1)}(s)=\Lambda_a^{(2)}(s)\,(\sqrt{M_a})^{s}G(s)L(a,s)$ and $\Lambda_a'^{(1)}(s)=\Lambda_a'^{(2)}(s)\,(\sqrt{M_a})^{s}G(s)L(\bar a,s)$, and likewise for $b$ with $M_b$; and with the functional equations $\Lambda_a^{(1)}(1-s)=w_a\Lambda_a'^{(1)}(s)$, $\Lambda_a^{(2)}(1-s)=\Lambda_a'^{(2)}(s)$, $\Lambda_b^{(1)}(1-s)=w_b\Lambda_b'^{(1)}(s)$, $\Lambda_b^{(2)}(1-s)=\Lambda_b'^{(2)}(s)$ for all complex $s$. Then $M_a=M_b$ and $P_p=Q_p$ for every $p\in S$.
--
--   This is the comparison principle underlying Deligne and Serre's treatment of weight-one forms (Lemme 4.9 and the proof of Théorème 4.6 of their paper): two Dirichlet series with Euler products, the same archimedean factor $G$, and functional equations relating $s$ to $1-s$ towards the conjugate series, which agree outside a finite set of primes, have equal levels and equal Euler factors everywhere. Here the second family is allowed the weaker local condition $\deg Q_p\le2$ with unit coefficient of $X^2$ at the bad primes. It is used in identifying the Euler factors and tame level of a weight-one newform whose $q$-coefficients are traces of a Galois representation, and it is proved by reduction to a statement about finite Euler products with a functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_eq_of_eulerProduct_completedLSeries_functionalEquation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem DeligneSerre.eq_of_eulerProduct_completedLSeries_functionalEquation
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (a b : ℕ → ℂ) (ha₁ : a 1 = 1) (hb₁ : b 1 = 1)
    (hamul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hbmul : ∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n)
    (P Q : ℕ → ℂ[X])
    (hP : ∀ p : ℕ, p.Prime → (P p : PowerSeries ℂ) * PowerSeries.mk (fun k => a (p ^ k)) = 1)
    (hQ : ∀ p : ℕ, p.Prime → (Q p : PowerSeries ℂ) * PowerSeries.mk (fun k => b (p ^ k)) = 1)
    (hPQ : ∀ p : ℕ, p.Prime → p ∉ S → P p = Q p)
    (hProots : ∀ p ∈ S, ∀ z : ℂ, (P p).IsRoot z → ‖z‖ = 1)
    (hQroots : ∀ p ∈ S,
      (∀ z : ℂ, (Q p).IsRoot z → 1 < ‖z‖ ^ 2 * p) ∨
        ((Q p).natDegree ≤ 2 ∧ ‖(Q p).coeff 2‖ = 1))
    (Ma Mb : ℕ) (hMa : Ma ≠ 0) (hMb : Mb ≠ 0)
    (hMS : ∀ p : ℕ, p.Prime → p ∣ Ma * Mb → p ∈ S)
    (G : ℂ → ℂ) (σ₁ : ℝ) (hG : ∀ s : ℝ, σ₁ < s → G s ≠ 0)
    (hsum : ∀ s : ℝ, σ₁ < s → LSeriesSummable a s ∧ LSeriesSummable b s)
    (wa wb : ℂ) (hwa : wa ≠ 0) (hwb : wb ≠ 0)
    (Λa₁ Λa₂ Λa₁' Λa₂' Λb₁ Λb₂ Λb₁' Λb₂' : ℂ → ℂ)
    (hΛa₁ : Differentiable ℂ Λa₁) (hΛa₂ : Differentiable ℂ Λa₂)
    (hΛa₁' : Differentiable ℂ Λa₁') (hΛa₂' : Differentiable ℂ Λa₂')
    (hΛb₁ : Differentiable ℂ Λb₁) (hΛb₂ : Differentiable ℂ Λb₂)
    (hΛb₁' : Differentiable ℂ Λb₁') (hΛb₂' : Differentiable ℂ Λb₂')
    (hΛa : ∀ s : ℝ, σ₁ < s →
      Λa₂ s ≠ 0 ∧ Λa₂' s ≠ 0 ∧
      Λa₁ s = Λa₂ s * (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries a s) ∧
      Λa₁' s = Λa₂' s *
        (((Real.sqrt Ma : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries (fun m => starRingEnd ℂ (a m)) s))
    (hΛb : ∀ s : ℝ, σ₁ < s →
      Λb₂ s ≠ 0 ∧ Λb₂' s ≠ 0 ∧
      Λb₁ s = Λb₂ s * (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries b s) ∧
      Λb₁' s = Λb₂' s *
        (((Real.sqrt Mb : ℝ) : ℂ) ^ (s : ℂ) * G s * LSeries (fun m => starRingEnd ℂ (b m)) s))
    (hFEa₁ : ∀ s : ℂ, Λa₁ (1 - s) = wa * Λa₁' s) (hFEa₂ : ∀ s : ℂ, Λa₂ (1 - s) = Λa₂' s)
    (hFEb₁ : ∀ s : ℂ, Λb₁ (1 - s) = wb * Λb₁' s) (hFEb₂ : ∀ s : ℂ, Λb₂ (1 - s) = Λb₂' s) :
    Ma = Mb ∧ ∀ p ∈ S, P p = Q p := by sorry
