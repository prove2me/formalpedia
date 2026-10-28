-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_19
-- name    : CerfCloning.Isotropic.eq_3_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:39.997035+00:00
-- url     : https://prove2.me/theorems/1ea9302d-2b30-483f-903c-0f70bb172171
-- title:
--   Eq. (3.19), p. 15 — the dual of $\hat a P + a F$ is $\hat b P + b F$ with $\hat b = a$, $b = \hat a$
-- statement:
--   Let $N \ge 1$, let $\hat a, a \in \mathbb C$, and let $\alpha_{m,n} = \hat a\, P_{m,n} + a\, F_{m,n}$ be the isotropic amplitudes of Eq. (3.16), with $P_{m,n} = \delta_{m,0}\delta_{n,0}$ and $F_{m,n} = 1/N$. Then the dual amplitudes $\beta_{m,n} = \frac1N\sum_{x,y} e^{2\pi i(nx-my)/N}\alpha_{x,y}$ of Eq. (3.11) are again isotropic, with the two components exchanged:
--   $$\beta_{m,n} = \hat b\, P_{m,n} + b\, F_{m,n}, \qquad \hat b = a, \quad b = \hat a .$$
--
--   Since $P$ and $F$ are Fourier duals, output $B$ of an isotropic Heisenberg cloner is again depolarizing, with fraction $\pi_b = |b|^2 = |\hat a|^2$. Together with (3.17) this gives the ellipse $|a|^2 + \frac2N\mathrm{Re}(ab^*) + |b|^2 = 1$ of Eq. (3.20).
--
--   Differences from the source:
--   - generalization: normalized amplitudes (3.17) → arbitrary $\hat a, a \in \mathbb C$; reason: the identity is linear and holds without normalization; adding it gives the source's statement.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 15, Eq. (3.19)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_19 (N : ℕ) [NeZero N] (ahat a : ℂ) :
    fourierDual N (isoAmplitude N ahat a) = isoAmplitude N a ahat := by sorry
end CerfCloning.Isotropic
