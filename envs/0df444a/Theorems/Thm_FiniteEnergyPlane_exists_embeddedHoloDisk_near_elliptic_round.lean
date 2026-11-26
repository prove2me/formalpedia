-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_embeddedHoloDisk_near_elliptic_round
-- name    : FiniteEnergyPlane.exists_embeddedHoloDisk_near_elliptic_round
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:10:15.879384+00:00
-- url     : https://prove2.me/theorems/d3963ae6-5c48-4fdb-9850-1ea77c019c2a
-- title:
--   Embedded holomorphic disks near an elliptic zero in the round sphere
-- statement:
--   Let $e$ embed $B_\rho$, $\rho>1$, into the round sphere $S^3\subset\mathbb{C}^2$, let $1<r<\rho$, and let $z_0\in B_r$ be a positive elliptic zero of its characteristic field. Let $\varepsilon>0$. In every neighbourhood of $z_0$ there are a neighbourhood $W$ of $z_0$ and a smooth $e'$ that embeds $B_r$ into $S^3$ such that
--
--   1. $e'=e$ near every point off $W$, $e'(z_0)=e(z_0)$, and $|e'-e|\le\varepsilon$;
--   2. $z_0$ is the only zero in $W$ of the characteristic field of $e'$, it is positive and nicely elliptic, and all leaves of $e'$ through $W$ issue from $z_0$ within $W$;
--   3. there is an embedded holomorphic disk $u$ with boundary loop in $e'(W)$, winding once around $e'(z_0)$.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$, and holomorphic refers to the standard structure $j_0$ on the symplectization $\mathbb{R}\times S^3\cong\mathbb{C}^2\setminus\{0\}$. The statement is the existence of holomorphic disks at an elliptic complex tangency.
--
--   **Formalization Note** The complex structure is `roundJ`. The source has a one-parameter family of disks; one disk is stated. Zeros, leaves and spanning disks are those of `FiniteEnergyPlane_DiskFoliation`; the characteristic field $V$ is `charField e`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorem 36 and Lemma 40

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Theorem 36, for the round sphere with the standard complex structure. Let `e` embed the disk of
radius `ρ` into the round sphere, let `1 < r < ρ`, and let `z₀` be a positive elliptic zero of its characteristic field in
the disk of radius `r`. Let `ε > 0`. In every neighbourhood of `z₀` there is a neighbourhood `W` of `z₀` and a disk `e'`, `ε`-close to `e`,
embedded on the disk of radius `r` and equal to `e` near every point off `W` and at `z₀`, for which `z₀` is a positive nicely
elliptic zero, the only zero in `W`, from which all leaves through `W` issue, such that there is an embedded
holomorphic disk with boundary loop in `e'(W)`, winding once around `e'(z₀)`. -/
theorem exists_embeddedHoloDisk_near_elliptic_round (e : ℂ → V 1) (ρ : ℝ)
    (he : IsEmbeddedDisk roundH e ρ) (r : ℝ) (hr : 1 < r) (hrρ : r < ρ)
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball (0 : ℂ) r) (h₀ : charField e z₀ = 0) (hdet : 0 < charDet e z₀)
    (htr : 0 < charTrace e z₀) (U : Set ℂ) (hU : U ∈ 𝓝 z₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ W ∈ 𝓝 z₀, W ⊆ U ∧ ∃ e' : ℂ → V 1, IsEmbeddedDisk roundH e' r ∧ (∀ z ∉ W, e' =ᶠ[𝓝 z] e) ∧
      e' z₀ = e z₀ ∧ (∀ z, ‖e' z - e z‖ ≤ ε) ∧ (∀ z ∈ W, charField e' z = 0 ↔ z = z₀) ∧ IsNicelyEllipticZero e' z₀ ∧
      0 < charTrace e' z₀ ∧ LeavesIssueFrom e' z₀ W ∧
      ∃ u : ℂ → V 1, IsEmbeddedHoloDisk roundH roundJ e' z₀ W u := by
  sorry

end FiniteEnergyPlane
