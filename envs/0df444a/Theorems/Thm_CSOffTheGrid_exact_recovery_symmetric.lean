-- Prove2me | Theorems.Thm_CSOffTheGrid_exact_recovery_symmetric
-- name    : CSOffTheGrid.exact_recovery_symmetric
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:27:27.503502+00:00
-- url     : https://prove2.me/theorems/5e447407-5e77-487d-955f-02c3e6f6b690
-- title:
--   Theorem 2.3 (as proved): exact recovery off the grid from $O(s\log s\log M)$ random samples
-- statement:
--   There is a numerical constant $C>0$ with the following property. Let $M\ge2$, $J=\{-2M,\dots,2M\}$, and let
--
--   $$x^\star_j=\sum_{k=1}^sc_ke^{i2\pi f_kj},\qquad j\in J,$$
--
--   with fixed frequencies $f_1,\dots,f_s\in[0,1]$ satisfying $\Delta_f\ge1/M$ (wrap-around distance) and fixed magnitudes $|c_k|>0$. Assume that the signs $\operatorname{sign}(c_k)$ are i.i.d. from a symmetric distribution on the complex unit circle, and that $T\subseteq J$ of size $m\le|J|$ is selected uniformly at random, independently of the signs. If $\delta\in(0,1)$ and
--
--   $$m\ge C\max\Big\{\log^2\frac M\delta,\ s\log\frac s\delta\log\frac M\delta\Big\},$$
--
--   then with probability at least $1-\delta$, $x^\star$ is the unique optimizer of $\min\|x\|_{\mathcal A}$ subject to $x_j=x^\star_j$, $j\in T$.
--
--   **Formalization Note** The statement adds $M\ge2$. For $M=1$ it is false: with $s=1$ and $\delta$ close to $1$ the sample bound allows $m=1$, and one sample never determines $x^\star$. The bound is on the probability of failure. A symmetric law is a probability measure carried by the unit circle and invariant under $u\mapsto-u$, and $\log(s/\delta)$ for $s=0$ is read as $0$.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 2.1, Theorem 2.3, eq. (2.5), p. 7; proof in Section 4, pp. 15-29

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem exact_recovery_symmetric : ∃ C : ℝ, 0 < C ∧
    ∀ (M : ℕ), 2 ≤ M → ∀ (s : ℕ) (f : Fin s → ℝ), (∀ k, f k ∈ Set.Icc (0 : ℝ) 1) →
    IsSeparated f (1 / (M : ℝ)) → ∀ (r : Fin s → ℝ), (∀ k, 0 < r k) →
    ∀ (μ : Measure ℂ), IsSymmetricCircleLaw μ → ∀ (m : ℕ), m ≤ 4 * M + 1 →
    ∀ (δ : ℝ), 0 < δ → δ < 1 →
    C * max (Real.log (M / δ) ^ 2) (s * Real.log (s / δ) * Real.log (M / δ)) ≤ m →
    uniformFailureProb (symJ M) m s μ
      (fun T u => IsUniqueOptimizer (symJ M) T (signal (symJ M) f (fun k => (r k : ℂ) * u k)))
      ≤ ENNReal.ofReal δ := by sorry

end CSOffTheGrid
