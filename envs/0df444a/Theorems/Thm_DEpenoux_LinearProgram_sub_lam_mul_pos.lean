-- Prove2me | Theorems.Thm_DEpenoux_LinearProgram_sub_lam_mul_pos
-- name    : DEpenoux.LinearProgram.sub_lam_mul_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:01:09.769135+00:00
-- url     : https://prove2.me/theorems/20e1a2e8-3c31-4d14-959f-8ec899558cd2
-- title:
--   Eq. (5) — if $u-\lambda Pu\ge 0$, not all zero, and $P$ is indecomposable, then every $u_i>0$
-- statement:
--   Let $P$ be an $m \times m$ stochastic matrix (nonnegative entries, unit row sums) which is *indecomposable* (irreducible): for every pair of indices $i, k$ there is $n \ge 0$ with $(P^n)_{ik} > 0$. Let $0 < \lambda < 1$ and $u \in \mathbb{R}^m$. If
--   $$ u - \lambda P u \ge 0 \quad\text{and}\quad u - \lambda P u \ne 0, $$
--   then every component of $u$ is strictly positive: $u_i > 0$ for all $i$.
--
--   This is d'Epenoux's (5), the strict form of (4); it is what makes $u^*$ a strict vectorial maximum of the set $A$ in Section 5.
--
--   **Formalization Note** The paper writes "$P_J$ is indecomposable" and "$u > 0$". The Lean statement reads "indecomposable" as irreducibility of the matrix (every state reaches every state with positive probability in some number of steps, $n = 0$ allowed), and "$u > 0$" as every component positive. The weaker reading "a single closed class plus transient states" would make (5) false: for $P = \begin{pmatrix}1&0\\1&0\end{pmatrix}$ and $u = (0,1)$, $u - \lambda P u = (0,1)$ is nonnegative and nonzero, but $u_0 = 0$. "Not all components zero" is stated as the existence of one nonzero component of $u - \lambda P u$.
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), p. 100, Section 2, Eq. (5)

import Mathlib

namespace DEpenoux.LinearProgram

theorem sub_lam_mul_pos {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (hP0 : ∀ i k, 0 ≤ P i k) (hP1 : ∀ i, ∑ k, P i k = 1)
    (hirr : ∀ i k, ∃ n : ℕ, 0 < (P ^ n) i k)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (u : Fin m → ℝ)
    (h : ∀ i, 0 ≤ u i - lam * Matrix.mulVec P u i)
    (hne : ∃ i, u i - lam * Matrix.mulVec P u i ≠ 0) :
    ∀ i, 0 < u i := by sorry

end DEpenoux.LinearProgram
