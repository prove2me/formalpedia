-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_disk_nicelyElliptic
-- name    : FiniteEnergyPlane.exists_disk_nicelyElliptic
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:06:03.888719+00:00
-- url     : https://prove2.me/theorems/81c14435-866b-4503-ba0d-98a33d2b5f4a
-- title:
--   Nearby disks with a nicely elliptic zero
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level. Let $e$ embed $B_\rho$, $\rho>1$, into $S$, and let $1<r<\rho$. Let $z_0\in B_r$ be a positive elliptic zero of the characteristic field of $e$. In every neighbourhood of $z_0$ there are a neighbourhood $W$ of $z_0$ and a smooth $e'$ that embeds $B_r$ into $S$ such that
--
--   1. $e'=e$ near every point off $W$, and $e'(z_0)=e(z_0)$;
--   2. $z_0$ is the only zero in $W$ of the characteristic field of $e'$, and it is positive and nicely elliptic;
--   3. all leaves of $e'$ through $W$ issue from $z_0$ within $W$.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$. The type of a single zero is changed and no other zero is created.
--
--   **Formalization Note** Zeros, leaves and spanning disks are those of `FiniteEnergyPlane_DiskFoliation`; the characteristic field $V$ is `charField e`. The disk is embedded on the open disk of radius $\rho$, and the new one on the smaller disk of radius $r$. Property 3 is `LeavesIssueFrom e' z₀ W`. The source also states that the area of the modified region is unchanged; this is not asserted.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Lemma 40

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Lemma 40. Let `e` embed the disk of radius `ρ` into `S`, let `1 < r < ρ`, and let `z₀` be a
positive elliptic zero of its characteristic field in the disk of radius `r`. In every neighbourhood of `z₀` there
is a neighbourhood `W` of `z₀` and a disk `e'`, embedded on the disk of radius `r` and equal to `e` near every point
off `W` and at `z₀`, for which `z₀` is a positive nicely elliptic zero, the only zero in `W`, and from which all leaves
through `W` issue. -/
theorem exists_disk_nicelyElliptic (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (r : ℝ) (hr : 1 < r) (hrρ : r < ρ)
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball (0 : ℂ) r) (h₀ : charField e z₀ = 0) (hdet : 0 < charDet e z₀)
    (htr : 0 < charTrace e z₀) (U : Set ℂ) (hU : U ∈ 𝓝 z₀) :
    ∃ W ∈ 𝓝 z₀, W ⊆ U ∧ ∃ e' : ℂ → V 1, IsEmbeddedDisk H e' r ∧ (∀ z ∉ W, e' =ᶠ[𝓝 z] e) ∧
      e' z₀ = e z₀ ∧ (∀ z ∈ W, charField e' z = 0 ↔ z = z₀) ∧ IsNicelyEllipticZero e' z₀ ∧
      0 < charTrace e' z₀ ∧ LeavesIssueFrom e' z₀ W := by
  sorry

end FiniteEnergyPlane
