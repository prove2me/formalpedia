-- Prove2me | Theorems.Thm_CSOffTheGrid_caratheodory_toeplitz
-- name    : CSOffTheGrid.caratheodory_toeplitz
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:22:34.008006+00:00
-- url     : https://prove2.me/theorems/56d24e98-e475-474d-acd7-b108408a3bac
-- title:
--   Lemma 2.2: Carathéodory–Toeplitz Vandermonde decomposition
-- statement:
--   Let $J=\{0,\dots,n-1\}$ with $n\ge1$, or $J=\{-2M,\dots,2M\}$ with $M\ge1$. Every positive semidefinite (Hermitian) Toeplitz matrix $P=\operatorname{Toep}(u)$ on $J$ of rank $r$ can be written as
--
--   $$P=VDV^*,\qquad V=[a(f_1,0)\ \cdots\ a(f_r,0)],\qquad D=\operatorname{diag}(d_1,\dots,d_r),$$
--
--   with frequencies $f_k\in[0,1]$ and real $d_k>0$, i.e. $P=\sum_{k=1}^r d_k\,a(f_k,0)a(f_k,0)^*$.
--
--   This classical decomposition is the tool behind Propositions 2.1 and 2.7.
--
--   **Formalization Note** A positive semidefinite Toeplitz matrix is Hermitian, so it is $\operatorname{Toep}(u)$ for its first column $u$. The lemma is stated for the two index sets used in the paper.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 2, Lemma 2.2, p. 5

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem caratheodory_toeplitz (J : Finset ℤ)
    (hJ : (∃ n : ℕ, 0 < n ∧ J = stdJ n) ∨ (∃ M : ℕ, 0 < M ∧ J = symJ M)) (u : ℤ → ℂ) (hP : (toep J u).PosSemidef) :
    ∃ f d : Fin (toep J u).rank → ℝ, (∀ k, f k ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ k, 0 < d k) ∧
      toep J u = ∑ k, (d k : ℂ) • Matrix.vecMulVec (atom J (f k) 0) (star (atom J (f k) 0)) := by sorry

end CSOffTheGrid
