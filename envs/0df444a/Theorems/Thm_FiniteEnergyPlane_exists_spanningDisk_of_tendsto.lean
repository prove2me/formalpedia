-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_spanningDisk_of_tendsto
-- name    : FiniteEnergyPlane.exists_spanningDisk_of_tendsto
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:13:14.567157+00:00
-- url     : https://prove2.me/theorems/47c770a3-77fb-4b4b-a771-ddb86408908b
-- title:
--   Spanning disks in nearby levels
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $H_k\to H$ in $C^\infty_{loc}(\mathbb{R}^4)$, with strictly star-shaped levels $S_k=H_k^{-1}(1)$. Let $C$ be a set contained in all $S_k$, let $e$ be a spanning disk of $C$ in $S$, defined on $B_\rho$, whose characteristic field has exactly one zero, positive and nicely elliptic $z_0$, and let $1<r<\rho$ and $\eta>0$. Then there are spanning disks $e'_k$ of $C$ in $S_k$, defined on $B_r$, whose characteristic fields have exactly one zero $z_0$, positive and nicely elliptic, and for all large $k$
--   $$\mathrm{area}(e'_k)<\mathrm{area}(e)+\eta .$$
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$, and the area of a disk is $\int\max(\omega_0(\partial_se,\partial_te),0)$ over the open unit disk. The zero has the same parameter for all $k$.
--
--   **Formalization Note** The area is `diskArea`. The disks exist for every $k$, and only the inequality is for large $k$. In the sources the contact forms are $h_k\lambda$ on a fixed manifold.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, § 3.1

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), § 3.1 (nearby levels). Let `Hs k → H` in `C^∞_loc`, all levels strictly star-shaped, and let `C` be a set
in all the levels. A spanning disk of `C` in `S` whose characteristic field has exactly one zero, positive and nicely elliptic, gives
such spanning disks of `C` in the levels of `Hs k`, with area at most that of the given disk plus any `η > 0` for large `k`. -/
theorem exists_spanningDisk_of_tendsto (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (Hs : ℕ → V 1 → ℝ) (hHs : ∀ k, IsStrictlyStarShapedLevel (Hs k))
    (hconv : ∀ m : ℕ, ∀ K : Set (V 1), IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) atTop K)
    (C : Set (V 1)) (hC : ∀ k, ∀ y ∈ C, Hs k y = 1) (e : ℂ → V 1) (ρ : ℝ) (he : IsSpanningDisk H C e ρ)
    (z₀ : ℂ) (hz₀ : HasNicelyEllipticPoint e z₀ ρ) (r : ℝ) (hr : 1 < r) (hrρ : r < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ e' : ℕ → ℂ → V 1,
      (∀ k, IsSpanningDisk (Hs k) C (e' k) r ∧ HasNicelyEllipticPoint (e' k) z₀ r) ∧
      ∀ᶠ k in atTop, diskArea (e' k) < diskArea e + ENNReal.ofReal η := by
  sorry

end FiniteEnergyPlane
