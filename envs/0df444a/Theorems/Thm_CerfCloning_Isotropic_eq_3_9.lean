-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_9
-- name    : CerfCloning.Isotropic.eq_3_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:36.538797+00:00
-- url     : https://prove2.me/theorems/eaa2157d-2c5b-4587-8517-ac991b840420
-- title:
--   Eq. (3.9), p. 14 — tracing (3.8) over $B$ and $C$: $\rho_{RA} = \sum_{m,n}|\alpha_{m,n}|^2|\psi_{m,n}\rangle\langle\psi_{m,n}|$
-- statement:
--   Let $N \ge 1$, let $\alpha_{m,n} \in \mathbb C$ for $m, n \in \mathbb Z_N$, and let
--   $|\Psi\rangle_{RA;BC} = \sum_{m,n} \alpha_{m,n}\, |\psi_{m,n}\rangle_{RA}\, |\psi_{m,N-n}\rangle_{BC}$ be the double-ME state of Eq. (3.8) of four $N$-level systems $R, A, B, C$. Then tracing over $B$ and $C$ leaves a mixture of maximally entangled states of $R$ and $A$:
--   $$\rho_{RA} = \operatorname{Tr}_{BC} |\Psi\rangle\langle\Psi| = \sum_{m,n=0}^{N-1} |\alpha_{m,n}|^2\, |\psi_{m,n}\rangle\langle\psi_{m,n}| .$$
--
--   By Eq. (3.6), output $A$ of the cloner described by $|\Psi\rangle$ is therefore the Heisenberg channel with error probabilities $p_{m,n} = |\alpha_{m,n}|^2$.
--
--   **Formalization Note** $|\Psi\rangle$ is a function on $((R,A),(B,C))$ and $\rho_{RA}(x,y) = \sum_z \Psi(x,z)\,\overline{\Psi(y,z)}$.
--
--   Differences from the source:
--   - generalization: amplitudes with $\sum_{m,n}|\alpha_{m,n}|^2 = 1$ → arbitrary complex amplitudes; reason: the identity is homogeneous of degree two in $\alpha$ and holds without normalization; adding it gives the source's statement.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 14, Eqs. (3.8)–(3.9)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_9 (N : ℕ) [NeZero N] (α : Fin N → Fin N → ℂ) :
    reducedRA (hcmState N α) =
      ∑ m, ∑ n, ((‖α m n‖ ^ 2 : ℝ) : ℂ) • pureDensity (meState N m n) := by sorry
end CerfCloning.Isotropic
