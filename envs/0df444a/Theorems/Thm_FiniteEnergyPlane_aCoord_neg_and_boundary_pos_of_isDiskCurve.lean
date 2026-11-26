-- Prove2me | Theorems.Thm_FiniteEnergyPlane_aCoord_neg_and_boundary_pos_of_isDiskCurve
-- name    : FiniteEnergyPlane.aCoord_neg_and_boundary_pos_of_isDiskCurve
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T20:35:53.391739+00:00
-- url     : https://prove2.me/theorems/57a98e7b-19b4-57ca-afb1-da414aac6776
-- title:
--   Disks with boundary on a surface in $\{0\}\times S$ lie below it and have a positively transverse boundary
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $e$ embed the disk of radius $\rho>1$ into $S$, let $A\subset B_\rho$, $z_0\in\mathbb{C}$, and let $u$ be a punctured $\tilde J$-holomorphic disk with punctures $\Gamma$ and boundary loop in $e(A)$ of winding number $1$ around $e(z_0)$. Let $a=\mathrm{aCoord}\circ u$ be its $\mathbb{R}$-coordinate, and suppose $a\to-\infty$ at every puncture. Then:
--
--   1. $a<0$ on $\mathring D\setminus\Gamma$;
--   2. for all $t$,
--   $$\lambda_0\Big(\frac{d}{dt}u(e^{2\pi it})\Big)>0;$$
--   3. if $\Gamma=\emptyset$, then $\int u^*d\lambda>0$.
--
--   Here $\mathring D$ is the open unit disk. The boundary loop lies in $\{0\}\times S$, and 2 says that it is positively transverse to $\xi$; in particular it avoids the zeros of the characteristic field.
--
--   **Formalization Note** The punctured disk is `IsDiskCurve H J e z₀ A Γ u`, with boundary condition stated for a loop in the parameter plane. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Lemma 19; H. Hofer, K. Wysocki, E. Zehnder, A characterisation of the tight three-sphere, Duke Math. J. 81 (1995), 159–226, Lemma 2.2

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Lemma 19; Hofer–Wysocki–Zehnder (1995), Lemma 2.2. Let `u` be a punctured `J̃`-holomorphic
disk with boundary on an embedded disk `e`, with `a → -∞` at every puncture. Then `a < 0` in the interior, and
the boundary loop of `u` is positively transverse to `ξ`. If there are no punctures, then `∫ u*dλ > 0`. -/
theorem aCoord_neg_and_boundary_pos_of_isDiskCurve (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ)
    (z₀ : ℂ) (A : Set ℂ) (hA : A ⊆ ball 0 ρ) (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsDiskCurve H J e z₀ A Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    (∀ z ∈ ball (0 : ℂ) 1 \ Γ, aCoord H (u z) < 0) ∧
      (∀ t : ℝ, 0 < liouville (u (ccwLoop 1 t)) (deriv (fun s => u (ccwLoop 1 s)) t)) ∧
      (Γ = ∅ → 0 < dlambdaEnergy H (ball 0 1) u) := by
  sorry

end FiniteEnergyPlane
