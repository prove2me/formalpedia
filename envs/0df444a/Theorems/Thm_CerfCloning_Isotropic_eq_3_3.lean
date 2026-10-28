-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_3
-- name    : CerfCloning.Isotropic.eq_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:21.378695+00:00
-- url     : https://prove2.me/theorems/227f195e-cc62-44d6-add3-cdad9c84d15a
-- title:
--   Eq. (3.3), p. 13 — the $N^2$ states $|\psi_{m,n}\rangle$ are orthonormal and $\sum_{m,n}|\psi_{m,n}\rangle\langle\psi_{m,n}| = \mathbb 1 \otimes \mathbb 1$
-- statement:
--   Let $N \ge 1$ and let $|\psi_{m,n}\rangle = N^{-1/2}\sum_{j} e^{2\pi i\, jn/N} |j\rangle|j+m\rangle$, $m, n \in \mathbb Z_N$, be the maximally entangled states of two $N$-level systems (Eq. (3.1)). Then they form an orthonormal basis:
--
--   1. $\langle \psi_{m,n} | \psi_{m',n'} \rangle = \delta_{m,m'}\,\delta_{n,n'}$ for all $m, n, m', n'$;
--   2. the resolution of identity holds:
--   $$\sum_{m,n=0}^{N-1} |\psi_{m,n}\rangle\langle\psi_{m,n}| = \mathbb 1_A \otimes \mathbb 1_B .$$
--
--   The states $|\psi_{m,n}\rangle$ generalize the four Bell states to $N$ dimensions; this basis is the one in which Heisenberg channels and Heisenberg cloning machines are described.
--
--   **Formalization Note** The inner product is conjugate-linear in its first argument; $\mathbb 1_A \otimes \mathbb 1_B$ is the identity matrix on `Fin N × Fin N`.
--
--   Differences from the source: none.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 13, Eq. (3.3)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_3 (N : ℕ) [NeZero N] :
    (∀ m n m' n' : Fin N, inner ℂ (meState N m n) (meState N m' n') =
        if m = m' ∧ n = n' then 1 else 0) ∧
    ∑ m, ∑ n, pureDensity (meState N m n) = 1 := by sorry
end CerfCloning.Isotropic
