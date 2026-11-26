-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_specialSpanningDisk
-- name    : FiniteEnergyPlane.exists_specialSpanningDisk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:15:12.48994+00:00
-- url     : https://prove2.me/theorems/763e35ca-e4a4-4242-9eee-ea87dca12a6c
-- title:
--   Special spanning disks at a fixed contact form
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$, all of whose periodic Reeb orbits are nondegenerate. Let $P=(x,T)$ be a prime periodic Reeb orbit with $\mu_{CZ}(P)\ge3$, and let $e$ be a spanning disk of $x(\mathbb{R})$ whose characteristic field has exactly one zero, positive and nicely elliptic, with
--   $$\int_{|z|<1}\max\big(\omega_0(\partial_se,\partial_te),0\big)\,ds\,dt<C .$$
--   Then there is a special spanning disk $e'$ for $P$ that satisfies the same inequality.
--
--   A special spanning disk for $P$ has, in addition to the properties of $e$, leaves that all issue from the zero and reach the boundary; moreover the Reeb field is not tangent to it near the boundary, and it contains no periodic Reeb orbit other than $x(\mathbb{R})$.
--
--   **Formalization Note** The conclusion is `IsSpecialSpanningDisk` of `FiniteEnergyPlane_SpanningDisk`, and the integral is `diskArea`. Periods are those of `ReebOrbit H`, not necessarily minimal, so multiple covers count. The index condition is for $P$ only, and is `IsCZAtLeast 3`. The source considers a sequence of contact forms.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Lemma 3.3

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), Lemma 3.3, at a fixed contact form. Let `P` be a prime periodic Reeb orbit with a
spanning disk of area less than `C` whose characteristic field has exactly one zero, positive and nicely elliptic. If every
periodic Reeb orbit is nondegenerate and `P` has Conley–Zehnder index at least `3`, then `P` has a special spanning disk of area less than `C`. -/
theorem exists_specialSpanningDisk (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (hP : P.IsPrime) (C : ℝ)
    (hnd : ∀ Q : ReebOrbit H, Q.IsNondegenerate) (hcz : P.IsCZAtLeast 3)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsSpanningDisk H (Set.range P.x) e ρ) (z₀ : ℂ)
    (hz₀ : HasNicelyEllipticPoint e z₀ ρ) (hC : diskArea e < ENNReal.ofReal C) :
    ∃ (e' : ℂ → V 1) (z₁ : ℂ), IsSpecialSpanningDisk H P e' z₁ ∧ diskArea e' < ENNReal.ofReal C := by
  sorry

end FiniteEnergyPlane
