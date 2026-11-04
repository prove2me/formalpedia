-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv_exterior
-- name    : FiniteEnergyPlane.isFiniteEnergyCurve_comp_inv_exterior
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T09:38:10.207822+00:00
-- url     : https://prove2.me/theorems/5ad4d39f-a65f-4df3-ab87-bea69cd5491a
-- title:
--   A finite-energy curve near infinity, read on a punctured disc via $z\mapsto z^{-1}$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, let $J$ be a compatible complex structure on $\xi$ and $\tilde J$ the induced almost complex structure on $\mathbb{R}^{2n+2}\setminus\{0\}\cong\mathbb{R}\times S$. Let $R\in\mathbb{R}$, and let $u$ be a finite-energy $\tilde J$-holomorphic curve on the exterior region $\{z\in\mathbb{C}: |z|>R\}$ (smooth, avoiding $0$, $\tilde J$-holomorphic, with finite Hofer energy). Let $\rho>0$ with $R\rho\le 1$. Then $v(z)=u(z^{-1})$ is a finite-energy $\tilde J$-holomorphic curve on the punctured disc $B(0,\rho)\setminus\{0\}$, and for every $z\neq 0$ with $|z^{-1}|>R$,
--   $$v^*d\lambda\ \text{density at } z \;=\; |z|^{-4}\cdot\big(u^*d\lambda\ \text{density at } z^{-1}\big),$$
--   where the $d\lambda$-density of $u$ at $z$ is $\omega_0(\partial_s w,\partial_t w)$ with $w=\mathrm{pr}\circ u$.
--
--   This lets statements about finite-energy curves near the puncture $0$ of a punctured disc be applied to a curve near its puncture at $\infty$. It extends the case of planes ($u$ defined on all of $\mathbb{C}$, unit disc) to curves defined only outside a disc.
--
--   **Formalization Note** $\mathbb{R}^{2n+2}$ is `V n`, $\tilde J$ is `Jtilde H J`, $\mathrm{pr}$ is `proj H`; "finite-energy curve on $U$" is `IsFiniteEnergyCurve H J U`, and the $d\lambda$-density is `dlambdaDensity H`. $R$ may be zero or negative, in which case the exterior region is $\mathbb{C}$ (for $R<0$) or $\mathbb{C}\setminus\{0\}$ (for $R=0$).
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder; U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2 (punctures at infinity; standard change of coordinates)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A finite-energy `J̃`-holomorphic curve on the exterior region `{|z| > R}`, read in the
coordinate `z ↦ z⁻¹`, is a finite-energy `J̃`-holomorphic curve on the punctured disc
`B(0, ρ) \ {0}` whenever `ρ > 0` and `R ρ ≤ 1`, and its `dλ`-density at `z` is `|z|⁻⁴` times the
density of `u` at `z⁻¹`. This is the domain version of `isFiniteEnergyCurve_comp_inv`, which treats
planes (`U = ℂ`). -/
theorem isFiniteEnergyCurve_comp_inv_exterior {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (R ρ : ℝ) (hρ : 0 < ρ) (hRρ : R * ρ ≤ 1) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J {z | R < ‖z‖} u) :
    IsFiniteEnergyCurve H J (ball 0 ρ \ {0}) (fun z => u z⁻¹) ∧
      ∀ z : ℂ, z ≠ 0 → R < ‖z⁻¹‖ →
        dlambdaDensity H (fun z => u z⁻¹) z = (‖z‖ ^ 4)⁻¹ * dlambdaDensity H u z⁻¹ := by
  sorry

end FiniteEnergyPlane
