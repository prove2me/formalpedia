-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_7
-- name    : CerfCloning.Isotropic.eq_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:26.346331+00:00
-- url     : https://prove2.me/theorems/ad6b8c93-71af-491c-807e-feaa5527fd8f
-- title:
--   Eq. (3.7), p. 13 — $(\mathbb 1 \otimes U_{m,n})|\psi_{0,0}\rangle = |\psi_{m,n}\rangle$
-- statement:
--   Let $N \ge 1$, let $|\psi_{m,n}\rangle$ be the maximally entangled states of Eq. (3.1) and $U_{m,n} = \sum_k e^{2\pi i\, kn/N}|k+m\rangle\langle k|$ the error operators of Eq. (3.5). For all $m, n \in \mathbb Z_N$, applying $U_{m,n}$ to the second system only maps $|\psi_{0,0}\rangle$ to $|\psi_{m,n}\rangle$:
--   $$(\mathbb 1 \otimes U_{m,n})\,|\psi_{0,0}\rangle = |\psi_{m,n}\rangle .$$
--
--   This is the correspondence between the $N^2$ error operators of a Heisenberg channel and the $N^2$ maximally entangled states, which turns a Heisenberg channel acting on half of $|\psi_{0,0}\rangle$ into a mixture of the states $|\psi_{m,n}\rangle$.
--
--   **Formalization Note** $\mathbb 1 \otimes U_{m,n}$ is the Kronecker product of matrices with the untouched system as the first factor, applied to $|\psi_{0,0}\rangle$ as a coordinate vector.
--
--   Differences from the source: none.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 13, Eq. (3.7)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_7 (N : ℕ) [NeZero N] (m n : Fin N) :
    (Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) (weyl N m n)) *ᵥ
        (meState N 0 0 : Fin N × Fin N → ℂ) =
      (meState N m n : Fin N × Fin N → ℂ) := by sorry
end CerfCloning.Isotropic
