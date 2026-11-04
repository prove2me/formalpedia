-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_affine
-- name    : FiniteEnergyPlane.isFiniteEnergyCurve_comp_affine
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T09:19:28.294477+00:00
-- url     : https://prove2.me/theorems/68025236-f796-4e57-b403-85176f3c0a06
-- title:
--   A finite-energy curve on a punctured disc, read on the punctured unit disc
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$, let $J$ be a complex structure on $\xi$ and $\tilde J$ the induced almost complex structure on $\mathbb{R}^{2n+2}\setminus\{0\}\cong\mathbb{R}\times S$. Let $z_0\in\mathbb{C}$, $r>0$, and let $u$ be a finite-energy $\tilde J$-holomorphic curve on the punctured disc $B(z_0,r)\setminus\{z_0\}$ (smooth, avoiding $0$, $\tilde J$-holomorphic, with finite Hofer energy). Then $\tilde u(z)=u(z_0+rz)$ is a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc $B(0,1)\setminus\{0\}$, and for every $z\in\mathbb{C}$
--   $$D(\mathrm{pr}\circ\tilde u)(z)=r\,D(\mathrm{pr}\circ u)(z_0+rz).$$
--
--   This moves statements about finite-energy curves near the puncture $0$ of the unit disc to an arbitrary puncture $z_0$ of a disc of any radius.
--
--   **Formalization Note** $\mathbb{R}^{2n+2}$ is `V n`, $\tilde J$ is `Jtilde H J`, $\mathrm{pr}$ is `proj H`; "finite-energy curve on $U$" is `IsFiniteEnergyCurve H J U`. No hypothesis on $H$ or $J$ is needed.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder; U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2 (finite-energy curves near a puncture; standard change of coordinates)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A finite-energy `J̃`-holomorphic curve on the punctured disc `B(z₀, r) \ {z₀}`, read in the
coordinate `z ↦ z₀ + r z`, is a finite-energy `J̃`-holomorphic curve on the punctured unit disc,
and the derivative of its projection to `S` is `r` times that of `u` at `z₀ + r z`. -/
theorem isFiniteEnergyCurve_comp_affine {n : ℕ} (H : V n → ℝ) (J : V n → V n →L[ℝ] V n)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball z₀ r \ {z₀}) u) :
    IsFiniteEnergyCurve H J (ball 0 1 \ {0}) (fun z => u (z₀ + (r : ℂ) * z)) ∧
      ∀ z : ℂ, fderiv ℝ (fun z => proj H (u (z₀ + (r : ℂ) * z))) z =
        r • fderiv ℝ (fun z => proj H (u z)) (z₀ + (r : ℂ) * z) := by
  sorry

end FiniteEnergyPlane
