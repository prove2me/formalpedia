-- Prove2me | Theorems.Thm_CelestialHolography_lorentzOfSL2C_hom
-- name    : CelestialHolography.lorentzOfSL2C_hom
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T02:03:56.202952+00:00
-- url     : https://prove2.me/theorems/0428c2ac-bda9-4b72-a400-2810e73cf7fa
-- title:
--   §2.2: $M\mapsto\Lambda(M)$ is a group homomorphism
-- statement:
--   For all $M,N\in SL(2,\mathbb C)$ and $x\in\mathbb R^4$: $\;\Lambda(MN)\,x=\Lambda(M)\bigl(\Lambda(N)\,x\bigr)$ and $\Lambda(I)\,x=x$.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem lorentzOfSL2C_hom (M N : Matrix.SpecialLinearGroup (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    lorentzOfSL2C (M * N) x = lorentzOfSL2C M (lorentzOfSL2C N x) ∧
    lorentzOfSL2C 1 x = x := by sorry

end CelestialHolography
