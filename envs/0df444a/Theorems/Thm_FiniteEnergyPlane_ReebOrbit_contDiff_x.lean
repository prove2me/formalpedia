-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
-- name    : FiniteEnergyPlane.ReebOrbit.contDiff_x
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T21:12:17.650969+00:00
-- url     : https://prove2.me/theorems/e13f168a-579b-43d4-a47e-0bb62b3a5cbe
-- title:
--   Periodic Reeb orbits on a star-shaped level are smooth
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $P=(x,T)$ a periodic Reeb orbit on $S$. Then $x:\mathbb{R}\to\mathbb{R}^{2n+2}$ is $C^\infty$.
--
--   This is the basic regularity of Reeb orbits, needed whenever derivatives of trivial cylinders $(s,t)\mapsto x(\sigma Tt+c)$ are estimated.
--
--   **Formalization Note** `ReebOrbit H` only records that $x$ has derivative $R(x(\tau))$ at every $\tau$; the conclusion is `ContDiff ℝ ∞ P.x`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, proof of Theorem 1.3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open scoped ContDiff

/-- The parametrization `x` of a periodic Reeb orbit on a strictly star-shaped level is `C^∞`. -/
theorem ReebOrbit.contDiff_x {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) : ContDiff ℝ ∞ P.x := by
  sorry

end FiniteEnergyPlane
