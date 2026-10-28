-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_gradNorm_le_of_plane
-- name    : FiniteEnergyPlane.exists_norm_mul_gradNorm_le_of_plane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T21:14:17.258994+00:00
-- url     : https://prove2.me/theorems/f441cde7-20c5-4a11-b766-f8d18fe71740
-- title:
--   Cylindrical gradient bound for finite-energy planes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, with associated almost complex structure $\tilde J$. Let $u:\mathbb C\to\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic plane. Then there is $C$ with
--   $$|z|\,|\nabla u(z)|\le C\qquad\text{for all }z\in\mathbb C .$$
--   Equivalently, in the cylindrical coordinates $z=e^{2\pi(s+it)}$ the map $(s,t)\mapsto u(e^{2\pi(s+it)})$ has bounded gradient.
--
--   **Formalization Note** $|\nabla u|$ is the $\mathbb R$-invariant norm `gradNorm H u` $=\|D(a\circ u)\|+\|D(\mathrm{proj}\circ u)\|$, where $a$ is `aCoord H` and $\mathrm{proj}$ is `proj H`. "Finite-energy plane" is `IsFiniteEnergyCurve H J Set.univ u`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Proposition 30, p. 537

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Gradient bound of a finite-energy plane in cylindrical coordinates (Hofer 1993, Prop. 30,
p. 537). For a finite-energy `J̃`-holomorphic plane `u`, the quantity `|z| · |∇u(z)|`, with the
`ℝ`-invariant norm `gradNorm`, is bounded on `ℂ`. -/
theorem exists_norm_mul_gradNorm_le_of_plane {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u) :
    ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C := by
  sorry

end FiniteEnergyPlane
