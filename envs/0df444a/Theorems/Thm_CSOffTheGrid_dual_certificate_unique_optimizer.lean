-- Prove2me | Theorems.Thm_CSOffTheGrid_dual_certificate_unique_optimizer
-- name    : CSOffTheGrid.dual_certificate_unique_optimizer
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:24:27.725572+00:00
-- url     : https://prove2.me/theorems/23ea3126-ed59-40ba-8ea5-880538176b65
-- title:
--   Proposition 2.4: a dual polynomial certifies unique optimality
-- statement:
--   Let $J=\{0,\dots,n-1\}$ with $n\ge1$, or $J=\{-2M,\dots,2M\}$ with $M\ge1$. Let $T\subseteq J$, let $f_1,\dots,f_s\in[0,1]$ be distinct points of the circle, let $c_1,\dots,c_s\in\mathbb C\setminus\{0\}$ and $x^\star=\sum_k c_k a(f_k,0)$. Suppose there is $q\in\mathbb C^{|J|}$ whose dual polynomial $Q(f)=\langle q,a(f,0)\rangle=\sum_{j\in J}q_je^{-i2\pi jf}$ satisfies
--
--   1. $Q(f_k)=\operatorname{sign}(c_k)$ for every $k$;
--   2. $|Q(f)|<1$ for every $f\notin\Omega=\{f_1,\dots,f_s\}$;
--   3. $q_j=0$ for every $j\notin T$.
--
--   Suppose moreover that the restricted atoms $a(f_1,0)_T,\dots,a(f_s,0)_T$ (the entries of the atoms on $T$ only) are linearly independent. Then $x^\star$ is the unique optimizer of
--
--   $$\min_x\ \|x\|_{\mathcal A}\quad\text{subject to}\quad x_j=x^\star_j,\ j\in T.$$
--
--   The proofs of Theorems 1.1 and 2.3 consist in constructing such a certificate.
--
--   **Formalization Note** "$f\notin\Omega$" is read on the circle: $f$ is any real number at nonzero wrap-around distance from every $f_k$. Unique optimality means that every other feasible $x$ has strictly larger atomic norm. The linear independence of the restricted atoms is not in the printed proposition, but it is needed: the certificate forces every optimizer onto the frequencies $f_k$, and only this condition then forces its coefficients to be the $c_k$. Without it the statement is false. For example, take $J=\{0,1,2\}$, $T=\{0,2\}$, $f=(0,\tfrac12)$, $c=(1,1)$ and $q=(\tfrac12,0,\tfrac12)$. Then $q$ is a certificate, but $(2,2,2)$ agrees with $x^\star=(2,0,2)$ on $T$ and has atomic norm at most $2=\|x^\star\|_{\mathcal A}$. In the random settings of Theorems 1.1 and 2.3 the condition holds whenever the matrix $D$ of Section 4 is invertible.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 2.1, Proposition 2.4, eqs. (2.9)-(2.12), p. 8

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem dual_certificate_unique_optimizer (J : Finset ℤ)
    (hJ : (∃ n : ℕ, 0 < n ∧ J = stdJ n) ∨ (∃ M : ℕ, 0 < M ∧ J = symJ M))
    (T : Finset ℤ) (hT : T ⊆ J) {s : ℕ} (f : Fin s → ℝ) (hf : ∀ k, f k ∈ Set.Icc (0 : ℝ) 1)
    (hdist : ∀ k j, k ≠ j → wrapDist (f k) (f j) ≠ 0) (c : Fin s → ℂ) (hc : ∀ k, c k ≠ 0)
    (hinj : ∀ w : Fin s → ℂ,
      (∀ j : J, (j : ℤ) ∈ T → ∑ k, w k * atom J (f k) 0 j = 0) → w = 0)
    (q : J → ℂ) (hq : IsDualCertificate J T f c q) :
    IsUniqueOptimizer J T (signal J f c) := by sorry

end CSOffTheGrid
