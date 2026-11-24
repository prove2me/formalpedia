-- Prove2me | Theorems.Thm_CSOffTheGrid_atomicNorm_eq_sdp
-- name    : CSOffTheGrid.atomicNorm_eq_sdp
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T03:23:10.208727+00:00
-- url     : https://prove2.me/theorems/4bfa23e9-5d4a-4d36-9a1b-d77834db3bfd
-- title:
--   Proposition 2.1: semidefinite characterization of the atomic norm
-- statement:
--   Let $J=\{0,\dots,n-1\}$ with $n\ge1$, or $J=\{-2M,\dots,2M\}$ with $M\ge1$. For every $x\in\mathbb C^{|J|}$,
--
--   $$\|x\|_{\mathcal A}=\inf\Big\{\tfrac1{2|J|}\operatorname{trace}(\operatorname{Toep}(u))+\tfrac12t:\ \begin{bmatrix}\operatorname{Toep}(u)&x\\x^*&t\end{bmatrix}\succeq0\Big\},$$
--
--   where $\operatorname{Toep}(u)$ is the Hermitian Toeplitz matrix with first column $u$ and $t\in\mathbb R$.
--
--   This makes atomic norm minimization over the continuum of complex sinusoids a semidefinite program.
--
--   **Formalization Note** $u$ is passed as the sequence of sub-diagonal entries of $\operatorname{Toep}(u)$, and the trace is taken by its real part (it is real whenever the constraint holds).
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 2, Proposition 2.1, eq. (2.2), p. 5

import Mathlib
import Definitions.Def_CSOffTheGrid_Basic

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace CSOffTheGrid

theorem atomicNorm_eq_sdp (J : Finset ℤ)
    (hJ : (∃ n : ℕ, 0 < n ∧ J = stdJ n) ∨ (∃ M : ℕ, 0 < M ∧ J = symJ M)) (x : J → ℂ) :
    atomicNorm J x = sdpValue J x := by sorry

end CSOffTheGrid
