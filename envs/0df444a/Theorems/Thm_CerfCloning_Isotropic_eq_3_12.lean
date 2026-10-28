-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_12
-- name    : CerfCloning.Isotropic.eq_3_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:40.101138+00:00
-- url     : https://prove2.me/theorems/b434e299-196a-44e7-8e86-c82723e2fba0
-- title:
--   Eq. (3.12), p. 14 — tracing (3.8) over $A$ and $C$: $\rho_{RB} = \sum_{m,n}|\beta_{m,n}|^2|\psi_{m,n}\rangle\langle\psi_{m,n}|$
-- statement:
--   Let $N \ge 1$, let $\alpha_{m,n} \in \mathbb C$ for $m, n \in \mathbb Z_N$, let $|\Psi\rangle$ be the double-ME state of Eq. (3.8) and let $\beta_{m,n} = \frac1N \sum_{x,y} e^{2\pi i (nx-my)/N}\alpha_{x,y}$ be the dual amplitudes of Eq. (3.11). Then tracing over $A$ and $C$ leaves a mixture of maximally entangled states of $R$ and $B$:
--   $$\rho_{RB} = \operatorname{Tr}_{AC} |\Psi\rangle\langle\Psi| = \sum_{m,n=0}^{N-1} |\beta_{m,n}|^2\, |\psi_{m,n}\rangle\langle\psi_{m,n}| .$$
--
--   Hence output $B$ of the cloner is the Heisenberg channel with error probabilities $q_{m,n} = |\beta_{m,n}|^2$, which are tied to those of output $A$ through the Fourier relation (3.11).
--
--   **Formalization Note** $|\Psi\rangle$ is a function on $((R,A),(B,C))$; $\rho_{RB}(x,y) = \sum_z \Psi'(x,z)\,\overline{\Psi'(y,z)}$, where $\Psi'$ is $\Psi$ with the $A$ and $B$ coordinates exchanged.
--
--   Differences from the source:
--   - generalization: amplitudes with $\sum_{m,n}|\alpha_{m,n}|^2 = 1$ → arbitrary complex amplitudes; reason: the identity holds without normalization; adding it gives the source's statement.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 14, Eqs. (3.11)–(3.12)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_12 (N : ℕ) [NeZero N] (α : Fin N → Fin N → ℂ) :
    reducedRB (hcmState N α) =
      ∑ m, ∑ n, ((‖fourierDual N α m n‖ ^ 2 : ℝ) : ℂ) • pureDensity (meState N m n) := by sorry
end CerfCloning.Isotropic
