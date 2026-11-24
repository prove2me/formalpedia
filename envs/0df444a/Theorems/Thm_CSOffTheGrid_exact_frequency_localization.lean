-- Prove2me | Theorems.Thm_CSOffTheGrid_exact_frequency_localization
-- name    : CSOffTheGrid.exact_frequency_localization
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:25:09.879863+00:00
-- url     : https://prove2.me/theorems/f0240f5d-eaa1-4e0e-b8dd-90e648489d3c
-- title:
--   Proposition 2.5 (1)-(2): exact frequency localization from the dual SDP
-- statement:
--   Let $J=\{0,\dots,n-1\}$ with $n\ge1$, or $J=\{-2M,\dots,2M\}$ with $M\ge1$. Let $T\subseteq J$, let $f_1,\dots,f_s\in[0,1]$ be distinct points of the circle, let $c_k\ne0$, and let $x=\sum_k c_ka(f_k,0)$. Let $\mathcal D$ be the set of optimal solutions $(q,H)$ of the dual semidefinite program
--
--   $$\max_{q,H}\ \langle q_T,x_T\rangle_{\mathbb R}\ \text{ s.t. }\ \begin{bmatrix}H&-q\\-q^*&1\end{bmatrix}\succeq0,\ \ \sum_{k}H_{k,k+j}=\begin{cases}1,&j=0\\0,&j=1,\dots,|J|-1\end{cases},\ \ H=H^*,\ \ q_{T^c}=0.$$
--
--   Suppose some $(q,H)\in\mathcal D$ has a dual polynomial $Q(f)=\langle q,a(f,0)\rangle$ with $Q(f_k)=\operatorname{sign}(c_k)$ for all $k$ and $|Q(f)|<1$ for $f\ne f_k$. Then every $(q,H)$ in the relative interior of $\mathcal D$ satisfies
--
--   1. $\operatorname{rank}\begin{bmatrix}H&-q\\-q^*&1\end{bmatrix}+s=|J|+1$ (strict complementarity);
--   2. $Q(f_k)=\operatorname{sign}(c_k)$ for all $k$ and $|Q(f)|<1$ for $f\ne f_k$.
--
--   Hence a dual optimum in the relative interior of $\mathcal D$ locates the frequencies exactly, as the points where $|Q|=1$.
--
--   **Formalization Note** The relative interior is Mathlib's intrinsic interior of $\mathcal D$, viewed as a subset of the real affine space $\mathbb C^{|J|}\times\mathbb C^{|J|\times|J|}$. Statement 3 of the proposition, convergence of the dual central path, is not included. The paper calls the primal optimum "unique" in statement 1, but the hypotheses do not imply this (see Proposition 2.4), and the statement here does not assume it.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 2.1, Proposition 2.5 (statements 1 and 2), eqs. (2.13)-(2.18), p. 10; proof in Appendix B, pp. 39-42

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem exact_frequency_localization (J : Finset ℤ)
    (hJ : (∃ n : ℕ, 0 < n ∧ J = stdJ n) ∨ (∃ M : ℕ, 0 < M ∧ J = symJ M))
    (T : Finset ℤ) (hT : T ⊆ J) {s : ℕ} (f : Fin s → ℝ) (hf : ∀ k, f k ∈ Set.Icc (0 : ℝ) 1)
    (hdist : ∀ k j, k ≠ j → wrapDist (f k) (f j) ≠ 0) (c : Fin s → ℂ) (hc : ∀ k, c k ≠ 0)
    (hex : ∃ p ∈ dualOptimalSet J T (signal J f c),
      (∀ k, dualPoly J p.1 (f k) = csign (c k)) ∧
      ∀ g : ℝ, (∀ k, wrapDist g (f k) ≠ 0) → ‖dualPoly J p.1 g‖ < 1) :
    ∀ p ∈ intrinsicInterior ℝ (dualOptimalSet J T (signal J f c)),
      (dualBlock J p.1 p.2).rank + s = J.card + 1 ∧
      (∀ k, dualPoly J p.1 (f k) = csign (c k)) ∧
      ∀ g : ℝ, (∀ k, wrapDist g (f k) ≠ 0) → ‖dualPoly J p.1 g‖ < 1 := by sorry

end CSOffTheGrid
