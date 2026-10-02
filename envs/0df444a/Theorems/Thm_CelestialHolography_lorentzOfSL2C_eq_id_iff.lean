-- Prove2me | Theorems.Thm_CelestialHolography_lorentzOfSL2C_eq_id_iff
-- name    : CelestialHolography.lorentzOfSL2C_eq_id_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T02:05:18.848839+00:00
-- url     : https://prove2.me/theorems/0b6854e9-a3fe-4666-9bd7-f5808a57d573
-- title:
--   §2.2: the kernel of $SL(2,\mathbb C)\to SO^+(1,3)$ is $\{\pm I\}$
-- statement:
--   For $M\in SL(2,\mathbb C)$: $\;\Lambda(M)$ is the identity of $\mathbb R^4$ if and only if $M=I$ or $M=-I$. Together with the homomorphism property this says $SL(2,\mathbb C)$ is a double cover of its image.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem lorentzOfSL2C_eq_id_iff (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (∀ x : Fin 4 → ℝ, lorentzOfSL2C M x = x) ↔ M = 1 ∨ M = -1 := by sorry

end CelestialHolography
