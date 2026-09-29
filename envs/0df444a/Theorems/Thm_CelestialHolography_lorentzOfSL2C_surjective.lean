-- Prove2me | Theorems.Thm_CelestialHolography_lorentzOfSL2C_surjective
-- name    : CelestialHolography.lorentzOfSL2C_surjective
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T02:05:46.368457+00:00
-- url     : https://prove2.me/theorems/32eca090-f0ca-4719-ac03-2eaeadfc07ca
-- title:
--   §2.2: every proper orthochronous Lorentz transformation comes from $SL(2,\mathbb C)$
-- statement:
--   Let $L:\mathbb R^4\to\mathbb R^4$ be a real-linear map preserving the Minkowski form, $\|Lx\|_\eta^2=\|x\|_\eta^2$, with $\det L=1$ and $(Le_0)^0>0$ (proper and orthochronous). Then $L=\Lambda(M)$ for some $M\in SL(2,\mathbb C)$.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem lorentzOfSL2C_surjective (L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hL : ∀ x, minkowskiNormSq (L x) = minkowskiNormSq x)
    (hdet : LinearMap.det L = 1) (horth : 0 < L (Pi.single 0 1) 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x, lorentzOfSL2C M x = L x := by sorry

end CelestialHolography
