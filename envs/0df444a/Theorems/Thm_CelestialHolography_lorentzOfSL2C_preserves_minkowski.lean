-- Prove2me | Theorems.Thm_CelestialHolography_lorentzOfSL2C_preserves_minkowski
-- name    : CelestialHolography.lorentzOfSL2C_preserves_minkowski
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T02:03:31.736831+00:00
-- url     : https://prove2.me/theorems/f8559018-052a-452f-b0fe-fe3021840687
-- title:
--   §2.2: $SL(2,\mathbb C)$ acts on $\mathbb R^{1,3}$ by Lorentz transformations
-- statement:
--   For every $M\in SL(2,\mathbb C)$ and every $x\in\mathbb R^4$, $\;\|\Lambda(M)x\|_\eta^2=\|x\|_\eta^2$, where $\Lambda(M)x=V(M\,H(x)\,M^\dagger)$. (Since $\det H(x)=-\|x\|^2_\eta$ and $\det M=1$.)
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem lorentzOfSL2C_preserves_minkowski (M : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x : Fin 4 → ℝ) : minkowskiNormSq (lorentzOfSL2C M x) = minkowskiNormSq x := by sorry

end CelestialHolography
