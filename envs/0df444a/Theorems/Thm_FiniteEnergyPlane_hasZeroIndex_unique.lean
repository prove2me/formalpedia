-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasZeroIndex_unique
-- name    : FiniteEnergyPlane.hasZeroIndex_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:58:34.259579+00:00
-- url     : https://prove2.me/theorems/bb0ef0f6-0cad-4def-a87a-c028f22ed51c
-- title:
--   Uniqueness of the local index of an isolated zero
-- statement:
--   Let $f:\mathbb{C}\to\mathbb{C}$ and $z_0\in\mathbb{C}$. If $z_0$ is an isolated zero of $f$ of local index $k$ and also of local index $m$, then $k=m$.
--
--   This makes the local index of an isolated zero a well-defined integer, so that index sums such as $\mathrm{wind}_\pi$ (Hryniewicz (14)) do not depend on the chosen witnesses.
--
--   **Formalization Note** "Isolated zero of local index $k$" is `HasZeroIndex f z₀ k`: $f(z_0)=0$, $f$ has no other zero in some `closedBall z₀ r` with $r>0$, and every counterclockwise circle $t\mapsto z_0+\rho e^{2\pi i t}$ with $0<\rho<r$ has winding number $k$ under $f$ (`HasLoopWind`).
-- source:
--   Standard (degree theory of loops in $\mathbb{C}^*$); used in U. Hryniewicz, Trans. AMS 364 (2012), Remark 3.20

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- The local index of an isolated zero of a function `ℂ → ℂ` is unique. -/
theorem hasZeroIndex_unique {f : ℂ → ℂ} {z₀ : ℂ} {k m : ℤ} (hk : HasZeroIndex f z₀ k)
    (hm : HasZeroIndex f z₀ m) : k = m := by
  sorry

end FiniteEnergyPlane
