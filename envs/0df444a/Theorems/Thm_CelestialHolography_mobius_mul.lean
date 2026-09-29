-- Prove2me | Theorems.Thm_CelestialHolography_mobius_mul
-- name    : CelestialHolography.mobius_mul
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T02:06:21.655833+00:00
-- url     : https://prove2.me/theorems/b2b8d286-0940-4024-8f27-6557cc2463d9
-- title:
--   Eq. (3): Möbius transformations compose like $SL(2,\mathbb C)$ matrices
-- statement:
--   For $M,N\in SL(2,\mathbb C)$ and $z\in\mathbb C$ at which neither $N$ nor $MN$ has its pole, $\;(MN)\cdot z=M\cdot(N\cdot z)$, where $M\cdot z=(az+b)/(cz+d)$.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem mobius_mul (M N : Matrix.SpecialLinearGroup (Fin 2) ℂ) (z : ℂ)
    (hN : N 1 0 * z + N 1 1 ≠ 0) (hMN : (M * N) 1 0 * z + (M * N) 1 1 ≠ 0) :
    mobius (M * N) z = mobius M (mobius N z) := by sorry

end CelestialHolography
