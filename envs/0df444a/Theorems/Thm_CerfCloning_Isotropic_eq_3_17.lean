-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_eq_3_17
-- name    : CerfCloning.Isotropic.eq_3_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:33.861909+00:00
-- url     : https://prove2.me/theorems/f2b52e94-93ec-4cf6-b8d2-f8237bb0d7aa
-- title:
--   Eq. (3.17), p. 15 — the norm of the isotropic amplitudes is $|\hat a|^2 + \frac2N\mathrm{Re}(\hat a a^*) + |a|^2$
-- statement:
--   Let $N \ge 1$, let $\hat a, a \in \mathbb C$, and let $\alpha_{m,n} = \hat a\, \delta_{m,0}\delta_{n,0} + a/N$ be the isotropic amplitudes of Eq. (3.16). Then
--   $$\sum_{m,n=0}^{N-1} |\alpha_{m,n}|^2 = |\hat a|^2 + \frac{2}{N}\,\mathrm{Re}(\hat a\, a^*) + |a|^2 .$$
--
--   Since $\sum_{m,n}|\alpha_{m,n}|^2 = |\hat a + a/N|^2 + (N^2-1)|a/N|^2$, this is the statement that the normalization condition of the double-ME state (3.8) for isotropic amplitudes can be written as $|\hat a|^2 + \frac2N \mathrm{Re}(\hat a a^*) + |a|^2 = 1$. With $\hat a = b$ it becomes the ellipse (3.20) on which the isotropic Heisenberg cloners lie.
--
--   **Formalization Note** $a^*$ is the complex conjugate `star a`; $|\cdot|^2$ is the squared complex modulus.
--
--   Differences from the source:
--   - reading: the peaked amplitude is printed $\bar a$ in (3.17) → $\hat a$; reason: (3.16) names it $\hat a$ and (3.17) restates the normalization of (3.16), so the printed bar is the hat of (3.16).
--   - encoding: left side $|\hat a + a/N|^2 + (N^2-1)|a/N|^2$ → $\sum_{m,n}|\alpha_{m,n}|^2$; reason: the two are the same number (one peaked entry, $N^2-1$ flat ones), and the sum is the normalization of (3.8).
--   - generalization: the equivalence of the two normalization conditions "$\cdots = 1$" → the identity of their left sides, for all $\hat a, a$; reason: the identity implies the equivalence.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 15, Eqs. (3.16)–(3.17)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem eq_3_17 (N : ℕ) [NeZero N] (ahat a : ℂ) :
    ∑ m, ∑ n, ‖isoAmplitude N ahat a m n‖ ^ 2 =
      ‖ahat‖ ^ 2 + 2 / (N : ℝ) * (ahat * star a).re + ‖a‖ ^ 2 := by sorry
end CerfCloning.Isotropic
