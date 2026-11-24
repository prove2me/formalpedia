-- Prove2me | Theorems.Thm_CSOffTheGrid_exact_recovery_general
-- name    : CSOffTheGrid.exact_recovery_general
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:28:01.84546+00:00
-- url     : https://prove2.me/theorems/f7ece583-90a8-4fb8-82ef-df8266a0873e
-- title:
--   Theorem 1.1 (as proved): recovery and frequency localization from random samples of $\{0,\dots,n-1\}$
-- statement:
--   There is a numerical constant $C>0$ with the following property. Let $n\ge5$, $J=\{0,\dots,n-1\}$, and observe
--
--   $$x^\star_j=\sum_{k=1}^sc_ke^{i2\pi f_kj},\qquad j=0,\dots,n-1,$$
--
--   on an index set $T\subseteq J$ of size $m\le n$ selected uniformly at random. The frequencies $f_1,\dots,f_s\in[0,1]$ are fixed with $\Delta_f\ge1/\lfloor(n-1)/4\rfloor$ (wrap-around distance), the magnitudes $|c_k|>0$ are fixed, and the signs $\operatorname{sign}(c_k)$ are i.i.d. uniform on the complex unit circle, independent of $T$. If $\delta\in(0,1)$ and
--
--   $$m\ge C\max\Big\{\log^2\frac n\delta,\ s\log\frac s\delta\log\frac n\delta\Big\},$$
--
--   then with probability at least $1-\delta$:
--
--   1. $x^\star$ is the unique optimizer of $\min\|x\|_{\mathcal A}$ subject to $x_j=x^\star_j$, $j\in T$ (equivalently, by Proposition 2.1, of the semidefinite program (2.6));
--   2. there is a dual certificate $q$ supported on $T$ whose polynomial $Q(f)=\sum_jq_je^{-i2\pi jf}$ satisfies $Q(f_k)=\operatorname{sign}(c_k)$ and $|Q(f)|<1$ for $f\notin\{f_1,\dots,f_s\}$, so the frequencies are the points where $|Q|=1$.
--
--   **Formalization Note** The paper's conclusion "recover $x^\star$ and localize the frequencies via a semidefinite program" is stated as what Appendix A proves: unique optimality together with a dual certificate. Exact localization by a solver's dual solution then follows from Proposition 2.5. The statement adds $n\ge5$, so that $\lfloor(n-1)/4\rfloor\ge1$ and the separation condition is meaningful.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 1, Theorem 1.1, eq. (1.1), p. 2; proof in Appendix A, pp. 37-38

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem exact_recovery_general : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 5 ≤ n → ∀ (s : ℕ) (f : Fin s → ℝ), (∀ k, f k ∈ Set.Icc (0 : ℝ) 1) →
    IsSeparated f (1 / (((n - 1) / 4 : ℕ) : ℝ)) → ∀ (r : Fin s → ℝ), (∀ k, 0 < r k) →
    ∀ (m : ℕ), m ≤ n → ∀ (δ : ℝ), 0 < δ → δ < 1 →
    C * max (Real.log (n / δ) ^ 2) (s * Real.log (s / δ) * Real.log (n / δ)) ≤ m →
    uniformFailureProb (stdJ n) m s uniformCircle
      (fun T u => IsUniqueOptimizer (stdJ n) T (signal (stdJ n) f (fun k => (r k : ℂ) * u k)) ∧
        ∃ q : stdJ n → ℂ, IsDualCertificate (stdJ n) T f (fun k => (r k : ℂ) * u k) q)
      ≤ ENNReal.ofReal δ := by sorry

end CSOffTheGrid
