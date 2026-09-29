-- Prove2me | Theorems.Thm_CelestialHolography_lorentzOfSL2C_orthochronous
-- name    : CelestialHolography.lorentzOfSL2C_orthochronous
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T02:04:30.492801+00:00
-- url     : https://prove2.me/theorems/64cc6349-5dbc-4d24-ae2f-a0d417feee1a
-- title:
--   §2.2: $\Lambda(M)$ is orthochronous
-- statement:
--   For every $M\in SL(2,\mathbb C)$ and every future-directed timelike $x$ ($x^0>0$, $\|x\|_\eta^2<0$), the image $\Lambda(M)x$ is again future-directed: $(\Lambda(M)x)^0>0$.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem lorentzOfSL2C_orthochronous (M : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x : Fin 4 → ℝ) (hx0 : 0 < x 0) (hx : minkowskiNormSq x < 0) :
    0 < lorentzOfSL2C M x 0 := by sorry

end CelestialHolography
