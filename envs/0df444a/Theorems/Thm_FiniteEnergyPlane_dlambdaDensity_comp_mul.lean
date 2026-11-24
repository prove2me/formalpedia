-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaDensity_comp_mul
-- name    : FiniteEnergyPlane.dlambdaDensity_comp_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T22:16:27.274794+00:00
-- url     : https://prove2.me/theorems/e0a6131b-ae23-4c5d-ad5c-507b81c423dd
-- title:
--   The $d\lambda$-density under complex scaling of the domain
-- statement:
--   Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$, $A,z\in\mathbb{C}$, and suppose that the projection $w=\mathrm{proj}_H\circ u$ is real differentiable at $Az$. Then the $d\lambda$-density $\omega_0(\partial_s w,\partial_t w)$ of $z\mapsto u(Az)$ at $z$ equals $|A|^2$ times that of $u$ at $Az$.
--
--   Pointwise companion of the change of variables for the $d\lambda$-energy; reusable for reparametrized curves.
--
--   **Formalization Note** The density is `dlambdaDensity`, and $|A|^2$ is `Complex.normSq A`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The `dλ`-density of `z ↦ u (A z)` at `z` is `|A|²` times the `dλ`-density of `u` at `A z`. -/
theorem dlambdaDensity_comp_mul {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (A z : ℂ)
    (hw : DifferentiableAt ℝ (fun y => proj H (u y)) (A * z)) :
    dlambdaDensity H (fun z => u (A * z)) z = Complex.normSq A * dlambdaDensity H u (A * z) := by
  sorry

end FiniteEnergyPlane
