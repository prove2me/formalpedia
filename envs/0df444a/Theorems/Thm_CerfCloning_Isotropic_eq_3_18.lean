-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_18
-- name    : CerfCloning.Isotropic.eq_3_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:44.378794+00:00
-- url     : https://prove2.me/theorems/f41cf1aa-35f6-438a-bc96-1a65352f6d74
-- title:
--   Eq. (3.18), p. 15 — for isotropic amplitudes, $\rho_{RA} = [|\hat a|^2 + \frac2N\mathrm{Re}(\hat a a^*)]\,|\psi_{0,0}\rangle\langle\psi_{0,0}| + |a|^2\,\mathbb 1\otimes\mathbb 1/N^2$
-- statement:
--   Let $N \ge 1$, let $\hat a, a \in \mathbb C$, let $\alpha_{m,n} = \hat a\,\delta_{m,0}\delta_{n,0} + a/N$ be the isotropic amplitudes of Eq. (3.16) and let $|\Psi\rangle$ be the double-ME state (3.8) with these amplitudes. Then tracing over $B$ and $C$ gives
--   $$\rho_{RA} = \Big[\,|\hat a|^2 + \frac{2}{N}\,\mathrm{Re}(\hat a\, a^*)\Big]\, |\psi_{0,0}\rangle\langle\psi_{0,0}| + |a|^2\, \frac{\mathbb 1 \otimes \mathbb 1}{N^2} .$$
--
--   Under the normalization (3.17) the first coefficient is $1 - |a|^2$, so $\rho_{RA}$ is the state that a depolarizing channel with fraction $\pi_a = |a|^2$ produces from half of $|\psi_{0,0}\rangle$: output $A$ of an isotropic Heisenberg cloner is depolarizing.
--
--   **Formalization Note** $\mathbb 1 \otimes \mathbb 1$ is the identity matrix on `Fin N × Fin N`; $\rho_{RA}$ is the unnormalized partial trace of $|\Psi\rangle\langle\Psi|$ over $(B, C)$.
--
--   Differences from the source:
--   - reading: the peaked amplitude is printed $\bar a$ in (3.18) → $\hat a$; reason: (3.18) traces the state with the amplitudes (3.16), whose peaked amplitude is $\hat a$.
--   - generalization: normalized amplitudes ($|\hat a|^2 + \frac2N\mathrm{Re}(\hat a a^*) + |a|^2 = 1$) → arbitrary $\hat a, a \in \mathbb C$; reason: the identity holds without normalization; adding it gives the source's statement.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 15, Eq. (3.18)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_18 (N : ℕ) [NeZero N] (ahat a : ℂ) :
    reducedRA (hcmState N (isoAmplitude N ahat a)) =
      (((‖ahat‖ ^ 2 + 2 / (N : ℝ) * (ahat * star a).re : ℝ)) : ℂ) • pureDensity (meState N 0 0) +
        ((‖a‖ ^ 2 / (N : ℝ) ^ 2 : ℝ) : ℂ) • 1 := by sorry
end CerfCloning.Isotropic
