-- Prove2me | Theorems.Thm_CSOffTheGrid_atomicL0_eq_rankValue
-- name    : CSOffTheGrid.atomicL0_eq_rankValue
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:23:46.357802+00:00
-- url     : https://prove2.me/theorems/6eef9bc9-9eeb-4572-9b19-9cbf37b45743
-- title:
--   Proposition 2.7: the atomic ℓ0 quantity equals a Toeplitz rank minimum
-- statement:
--   Let $J=\{0,\dots,n-1\}$ with $n\ge1$, or $J=\{-2M,\dots,2M\}$ with $M\ge1$. For every $x\in\mathbb C^{|J|}$, the least number of atoms needed to write $x$,
--
--   $$\|x\|_{\mathcal A,0}=\min\Big\{s:\ x=\sum_{k=1}^sc_ka(f_k,\phi_k),\ c_k\ge0,\ f_k\in[0,1],\ \phi_k\in[0,2\pi)\Big\},$$
--
--   equals the optimal value of
--
--   $$\min_{u,t}\ \operatorname{rank}(\operatorname{Toep}(u))\quad\text{subject to}\quad\begin{bmatrix}\operatorname{Toep}(u)&x\\x^*&t\end{bmatrix}\succeq0.$$
--
--   Thus atomic norm minimization is the trace relaxation of this rank minimization problem.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 2.2, Proposition 2.7, eq. (2.19), p. 11

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem atomicL0_eq_rankValue (J : Finset ℤ)
    (hJ : (∃ n : ℕ, 0 < n ∧ J = stdJ n) ∨ (∃ M : ℕ, 0 < M ∧ J = symJ M)) (x : J → ℂ) :
    atomicL0 J x = rankValue J x := by sorry

end CSOffTheGrid
