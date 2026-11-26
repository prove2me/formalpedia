-- Prove2me | Theorems.Thm_FiniteEnergyPlane_charField_eq_zero_of_periodic
-- name    : FiniteEnergyPlane.charField_eq_zero_of_periodic
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:11:50.781876+00:00
-- url     : https://prove2.me/theorems/180e66f6-401b-4b63-ab82-5ea83bd4e3a2
-- title:
--   The characteristic foliation of an embedded disk has no closed leaf
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $e$ embed $B_\rho$, $\rho>1$, into $S$, with characteristic field $V$. If $\sigma:\mathbb{R}\to B_\rho$ satisfies
--   $$\sigma'=V(\sigma),\qquad\sigma(\tau+T)=\sigma(\tau)\quad\text{for some }T>0,$$
--   then $V(\sigma(0))=0$, so $\sigma$ is constant.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$. This is the tightness of the standard contact structure of the three-sphere, in terms of characteristic foliations, for strictly star-shaped levels.
--
--   **Formalization Note** The notions of a tight contact structure and of an overtwisted disk are not introduced. If the boundary of an embedded disk is Legendrian and the disk is nowhere tangent to $\xi$ along it, the boundary is a closed leaf of every slightly larger disk, so the statement excludes such disks.
-- source:
--   D. Bennequin, Entrelacements et équations de Pfaff, Astérisque 107–108 (1983), 87–161; cf. H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Section 1

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Bennequin (1983); Hofer (1993), Theorem 5, for strictly star-shaped levels of `ℝ⁴`. The characteristic field of an
embedded disk in `S` has no nonconstant periodic integral curve. -/
theorem charField_eq_zero_of_periodic (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (σ : ℝ → ℂ) (T : ℝ) (hT : 0 < T) (hσ : IsCharCurve e σ)
    (hper : ∀ τ, σ (τ + T) = σ τ) (hσρ : Set.range σ ⊆ ball 0 ρ) : charField e (σ 0) = 0 := by
  sorry

end FiniteEnergyPlane
