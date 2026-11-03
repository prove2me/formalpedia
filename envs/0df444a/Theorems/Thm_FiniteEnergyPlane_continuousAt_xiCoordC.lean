-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousAt_xiCoordC
-- name    : FiniteEnergyPlane.continuousAt_xiCoordC
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-02T21:14:07.667088+00:00
-- url     : https://prove2.me/theorems/3525c527-a4a7-49b8-9ec9-cdcfeeb8d2cb
-- title:
--   Continuity of the global-frame coordinates of $\xi$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and, for $x\in\mathbb{R}^4$ and $v\in\mathbb{R}^4$, let $\psi_x(v)=\omega_0(v,Z_2(x))+i\,\omega_0(Z_1(x),v)\in\mathbb{C}$ be the coordinates of $v$ in Hryniewicz's global frame $Z_1,Z_2$ of $\xi$. If $X,Y:\mathbb{C}\to\mathbb{R}^4$ are continuous at $z_0$ and $X(z_0)\in S$, then $z\mapsto\psi_{X(z)}(Y(z))$ is continuous at $z_0$.
--
--   This lets winding numbers and zeros of $\xi$-valued maps along a curve in $S$ be studied through continuous $\mathbb{C}$-valued functions.
--
--   **Formalization Note** $\psi_x(v)$ is `xiCoordC H x v` from `FiniteEnergyPlane_Winding`; $\mathbb{R}^4$ is `V 1`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2 (global symplectic frame of the contact structure)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

/-- Let `S = H⁻¹(1)` be a strictly star-shaped level. If `X, Y : ℂ → V 1` are continuous at `z₀`
and `X(z₀) ∈ S`, then `z ↦ xiCoordC H (X z) (Y z)`, the coordinates of `Y(z)` in the global frame of
`ξ_{X(z)}`, is continuous at `z₀`. -/
theorem continuousAt_xiCoordC (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {X Y : ℂ → V 1} {z₀ : ℂ} (hX : ContinuousAt X z₀) (hY : ContinuousAt Y z₀)
    (hX1 : H (X z₀) = 1) : ContinuousAt (fun z => xiCoordC H (X z) (Y z)) z₀ := by
  sorry

end FiniteEnergyPlane
