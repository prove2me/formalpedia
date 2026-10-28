-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_6
-- name    : CerfCloning.Isotropic.eq_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:30.147492+00:00
-- url     : https://prove2.me/theorems/47335337-44bf-4f06-b3f6-f513b733d825
-- title:
--   Eq. (3.6), p. 13 — a Heisenberg channel on half of $|\psi_{0,0}\rangle$ gives $\rho_{RY} = \sum_{m,n} p_{m,n}|\psi_{m,n}\rangle\langle\psi_{m,n}|$
-- statement:
--   Let $N \ge 1$ and let $p_{m,n}$, $m, n \in \mathbb Z_N$, be real weights. Let $\mathcal H_p(\rho) = \sum_{m,n} p_{m,n}\, U_{m,n}\,\rho\, U_{m,n}^\dagger$ be the Heisenberg channel with these weights, where $U_{m,n}$ are the error operators of Eq. (3.5). If the input $X$ of the channel is maximally entangled with a reference $R$, i.e. the joint state is $|\psi_{0,0}\rangle = \sum_j |j\rangle|j\rangle/\sqrt N$, then the joint state of $R$ and the output $Y$ is
--   $$\rho_{RY} = (\mathrm{id}_R \otimes \mathcal H_p)\big(|\psi_{0,0}\rangle\langle\psi_{0,0}|\big) = \sum_{m,n} p_{m,n}\, |\psi_{m,n}\rangle\langle\psi_{m,n}| .$$
--
--   So a Heisenberg channel is characterized by the probability distribution of its error operators, read off as the weights of the maximally entangled states in $\rho_{RY}$.
--
--   **Formalization Note** $\mathrm{id}_R \otimes \mathcal H_p$ is `QAlgorithms.idTensorSuperop`, with $R$ the first factor.
--
--   Differences from the source:
--   - generalization: $p_{m,n}$ a probability distribution ($p_{m,n} \ge 0$, $\sum_{m,n} p_{m,n} = 1$) → any real weights $p_{m,n}$; reason: the identity is linear in $p$ and holds for all real weights, so it specializes to the source's channel by adding the two conditions.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 13, Eq. (3.6)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_6 (N : ℕ) [NeZero N] (p : Fin N → Fin N → ℝ) :
    idTensorSuperop (R := Fin N) (heisenbergChannel N p) (pureDensity (meState N 0 0)) =
      ∑ m, ∑ n, ((p m n : ℝ) : ℂ) • pureDensity (meState N m n) := by sorry
end CerfCloning.Isotropic
