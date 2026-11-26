-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_spanningDisk_no_periodicOrbit
-- name    : FiniteEnergyPlane.exists_spanningDisk_no_periodicOrbit
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:14:21.385712+00:00
-- url     : https://prove2.me/theorems/dd2fbab5-0284-54fb-93b0-154477c0eec6
-- title:
--   Spanning disks that contain no other periodic orbit
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, all of whose periodic Reeb orbits are nondegenerate. Let $P=(x,T)$ be a periodic Reeb orbit and $e$ a spanning disk of $x(\mathbb{R})$ whose characteristic field has exactly one zero, positive and nicely elliptic, of area less than $C$, such that $R$ is not tangent to $e$ at the points with $1-\delta<|z|<1$ for some $\delta>0$. Then there is a spanning disk $e'$ of $x(\mathbb{R})$ with the same properties such that
--   $$y(\mathbb{R})\subset e'(D)\ \Longrightarrow\ y(\mathbb{R})=x(\mathbb{R})\qquad\text{for every periodic Reeb orbit }(y,T').$$
--
--   Here $D$ is the closed unit disk, and the area of a disk is $\int\max(\omega_0(\partial_se,\partial_te),0)$ over the open unit disk. The orbits $y$ have arbitrary period.
--
--   **Formalization Note** The area is `diskArea`. Periods are those of `ReebOrbit H`, not necessarily minimal, so multiple covers count. The zero and $\delta$ of $e'$ may differ from those of $e$. The source considers a sequence of nondegenerate contact forms; here the form is fixed.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, § 5.2.3; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Lemma 3.3

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2012), § 5.2; Hryniewicz (2014), Lemma 3.3 (the last assertion), at a fixed contact form. Let `P` be a
periodic Reeb orbit with a spanning disk of area less than `C` whose characteristic field has exactly one
zero, positive and nicely elliptic, and to which the Reeb field is not tangent near the unit circle, inside the open disk.
If every periodic Reeb orbit is nondegenerate, there is such a spanning disk that contains no periodic
orbit other than `x(ℝ)`. -/
theorem exists_spanningDisk_no_periodicOrbit (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (C : ℝ) (hQ : ∀ Q : ReebOrbit H, Q.IsNondegenerate)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsSpanningDisk H (Set.range P.x) e ρ) (z₀ : ℂ)
    (hz₀ : HasNicelyEllipticPoint e z₀ ρ) (hC : diskArea e < ENNReal.ofReal C)
    (hR : ∃ δ > 0, ∀ z : ℂ, 1 - δ < ‖z‖ → ‖z‖ < 1 → reeb H (e z) ∉ Set.range (fderiv ℝ e z)) :
    ∃ (e' : ℂ → V 1) (ρ' : ℝ) (z₁ : ℂ), IsSpanningDisk H (Set.range P.x) e' ρ' ∧
      HasNicelyEllipticPoint e' z₁ ρ' ∧ diskArea e' < ENNReal.ofReal C ∧
      (∃ δ > 0, ∀ z : ℂ, 1 - δ < ‖z‖ → ‖z‖ < 1 → reeb H (e' z) ∉ Set.range (fderiv ℝ e' z)) ∧
      ∀ Q : ReebOrbit H, Set.range Q.x ⊆ e' '' closedBall 0 1 → Set.range Q.x = Set.range P.x := by
  sorry

end FiniteEnergyPlane
