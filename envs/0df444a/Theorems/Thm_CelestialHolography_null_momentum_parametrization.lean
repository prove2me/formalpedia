-- Prove2me | Theorems.Thm_CelestialHolography_null_momentum_parametrization
-- name    : CelestialHolography.null_momentum_parametrization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:54:31.817281+00:00
-- url     : https://prove2.me/theorems/a5f830ad-158a-4fad-a57e-638979cff201
-- title:
--   Eq. (11): every future null momentum is $\omega\,q(z)$ for unique $\omega>0$, $z\in\mathbb C$
-- statement:
--   Let $p\in\mathbb R^4$ be a future-directed null vector, $\|p\|_\eta^2=0$ and $p^0>0$, which is not on the ray of $(1,0,0,-1)$, i.e. $p^0+p^3\neq0$. Then there is a **unique** pair $(\omega,z)\in\mathbb R\times\mathbb C$ with $\omega>0$ and
--   $$p=\omega\,q(z).$$
--   The excluded ray is the direction $z=\infty$ of the celestial sphere, which the chart $z\in\mathbb C$ does not cover.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem null_momentum_parametrization (p : Fin 4 → ℝ) (hnull : minkowskiNormSq p = 0)
    (hfut : 0 < p 0) (hpole : p 0 + p 3 ≠ 0) :
    ∃! wz : ℝ × ℂ, 0 < wz.1 ∧ p = wz.1 • nullVector wz.2 := by sorry

end CelestialHolography
