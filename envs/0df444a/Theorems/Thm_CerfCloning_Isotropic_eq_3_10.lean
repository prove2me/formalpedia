-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_10
-- name    : CerfCloning.Isotropic.eq_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:30.311438+00:00
-- url     : https://prove2.me/theorems/d2847424-409f-4f6c-88fe-76d0c0b65b9b
-- title:
--   Eqs. (3.10)–(3.11), p. 14 — interchanging $A$ and $B$ turns (3.8) into the double-ME state with the dual amplitudes $\beta_{m,n}$
-- statement:
--   Let $N \ge 1$, let $\alpha_{m,n} \in \mathbb C$ for $m, n \in \mathbb Z_N$, and let $|\Psi\rangle_{RA;BC} = \sum_{m,n} \alpha_{m,n}\, |\psi_{m,n}\rangle_{RA}\, |\psi_{m,N-n}\rangle_{BC}$ (Eq. (3.8)). Define the dual amplitudes
--   $$\beta_{m,n} = \frac1N \sum_{x,y=0}^{N-1} e^{2\pi i (nx - my)/N}\, \alpha_{x,y} \qquad \text{(3.11)}.$$
--   Then the same four-partite vector, with the systems grouped as $(R,B)$ and $(A,C)$, is the double-ME state with amplitudes $\beta$:
--   $$|\Psi\rangle_{RB;AC} = \sum_{m,n=0}^{N-1} \beta_{m,n}\, |\psi_{m,n}\rangle_{RB}\, |\psi_{m,N-n}\rangle_{AC} \qquad \text{(3.10)}.$$
--
--   This is the complementarity between the two outputs of a Heisenberg cloning machine: the amplitudes that describe output $B$ are a two-dimensional discrete Fourier transform of those that describe output $A$.
--
--   **Formalization Note** The left side is the vector $\Psi$ of Eq. (3.8) with its $A$ and $B$ coordinates exchanged, so that it is read on $((R,B),(A,C))$; the right side is Eq. (3.8)'s construction applied to $\beta$. $N-n$ is $-n$ in $\mathbb Z_N$.
--
--   Differences from the source:
--   - generalization: amplitudes with $\sum_{m,n}|\alpha_{m,n}|^2 = 1$ → arbitrary complex amplitudes; reason: the identity is linear in $\alpha$ and holds without normalization; adding it gives the source's statement.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 14, Eqs. (3.10)–(3.11)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_10 (N : ℕ) [NeZero N] (α : Fin N → Fin N → ℂ) :
    swapAB (hcmState N α) = hcmState N (fourierDual N α) := by sorry
end CerfCloning.Isotropic
