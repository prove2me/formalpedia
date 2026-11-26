-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_spanningDisk_transverse_near_boundary
-- name    : FiniteEnergyPlane.exists_spanningDisk_transverse_near_boundary
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:13:44.379222+00:00
-- url     : https://prove2.me/theorems/d1ed739e-0e33-5cc6-aedf-1d1912eae226
-- title:
--   Spanning disks to which the Reeb field is not tangent near the boundary
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$. Let $P=(x,T)$ be a prime nondegenerate periodic Reeb orbit with $\mu_{CZ}(P)\ge3$, and let $e$ be a spanning disk of $x(\mathbb{R})$ whose characteristic field has exactly one zero, positive and nicely elliptic. For every $\eta>0$ there are a spanning disk $e'$ of $x(\mathbb{R})$ whose characteristic field has exactly one zero, positive and nicely elliptic, and $\delta>0$, with
--   $$\mathrm{area}(e')<\mathrm{area}(e)+\eta,\qquad R(e'(z))\notin De'(z)(\mathbb{C})\quad\text{for }1-\delta<|z|<1 .$$
--
--   The area of a disk is $\int\max(\omega_0(\partial_se,\partial_te),0)$ over the open unit disk. The disks meet $x(\mathbb{R})$, where they are tangent to $R$, only along their boundaries.
--
--   **Formalization Note** The index condition is `IsCZAtLeast 3`, in the global frame of $\xi$, and the area is `diskArea`. No self-linking number occurs among the hypotheses. The source has an orbit in a contact $3$-manifold and a disk equal to the given one off a neighbourhood of $x(\mathbb{R})$; the latter is not stated.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Proposition 5.1 and Theorem 5.5

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2012), Proposition 5.1. Let `P` be a prime nondegenerate periodic Reeb orbit of Conley–Zehnder index at
least `3` with a spanning disk whose characteristic field has exactly one zero, positive and nicely elliptic. There is such a
spanning disk, of area at most that of the given one plus any `η > 0`, to which the Reeb field is not tangent near the
unit circle, inside the open disk. -/
theorem exists_spanningDisk_transverse_near_boundary (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (hP : P.IsPrime) (hnd : P.IsNondegenerate) (hcz : P.IsCZAtLeast 3)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsSpanningDisk H (Set.range P.x) e ρ) (z₀ : ℂ)
    (hz₀ : HasNicelyEllipticPoint e z₀ ρ) (η : ℝ) (hη : 0 < η) :
    ∃ (e' : ℂ → V 1) (ρ' : ℝ) (z₁ : ℂ), IsSpanningDisk H (Set.range P.x) e' ρ' ∧
      HasNicelyEllipticPoint e' z₁ ρ' ∧ diskArea e' < diskArea e + ENNReal.ofReal η ∧
      (∃ δ > 0, ∀ z : ℂ, 1 - δ < ‖z‖ → ‖z‖ < 1 → reeb H (e' z) ∉ Set.range (fderiv ℝ e' z)) := by
  sorry

end FiniteEnergyPlane
