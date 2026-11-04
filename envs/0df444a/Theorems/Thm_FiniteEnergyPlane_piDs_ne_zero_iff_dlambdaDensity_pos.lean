-- Prove2me | Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
-- name    : FiniteEnergyPlane.piDs_ne_zero_iff_dlambdaDensity_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T09:12:26.026182+00:00
-- url     : https://prove2.me/theorems/68077964-b696-441e-a485-9c37890acb56
-- title:
--   The $\xi$-part of $\partial_s u$ vanishes exactly where the $d\lambda$-density vanishes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Liouville form $\lambda_0$, Reeb field $R$ and contact structure $\xi=\ker\lambda_0|_{TS}$, let $J$ be a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$. Let $U\subset\mathbb{C}$ be open and $u:U\to\mathbb{R}^4\setminus\{0\}$ be $\tilde J$-holomorphic, with $w=\mathrm{pr}\circ u:U\to S$. Then for every $z\in U$,
--   $$\pi\,\partial_s w(z)\neq 0\iff \omega_0\big(\partial_s w(z),\partial_t w(z)\big)>0,$$
--   where $\pi:TS\to\xi$ is the projection along $R$, and $\pi\,\partial_s w(z)$ is read in Hryniewicz's global frame of $\xi$.
--
--   So the zeros of $\pi\partial_s u$ are exactly the points where the integrand $u^*d\lambda$ vanishes, and elsewhere this integrand is positive. This lets statements about the $d\lambda$-density be transferred to the section $\pi\partial_s u$ and back.
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`, $\tilde J$ is `Jtilde H J`, $w=$ `proj H ∘ u`; $\pi\partial_s w$ in the global frame is `piDs H u z` (a complex number, `xiCoordC`), and $\omega_0(\partial_s w,\partial_t w)$ is `dlambdaDensity H u z`. The hypotheses only ask that $u$ avoid $0$ and be $\tilde J$-holomorphic on the open set $U$ (no energy bound).
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4 (zeros of $\pi\partial_s u$ and the integrand $u^*d\lambda$)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- At a point `z` of an open set `U` on which `u` avoids `0` and is `J̃`-holomorphic, the
`ξ`-component `π ∂ₛu(z)` is nonzero exactly when the `dλ`-density of `u` at `z` is positive. -/
theorem piDs_ne_zero_iff_dlambdaDensity_pos (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) {z : ℂ} (hz : z ∈ U) :
    piDs H u z ≠ 0 ↔ 0 < dlambdaDensity H u z := by
  sorry

end FiniteEnergyPlane
