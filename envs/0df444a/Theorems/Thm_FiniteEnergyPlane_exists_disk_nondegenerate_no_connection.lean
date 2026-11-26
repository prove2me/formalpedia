-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_disk_nondegenerate_no_connection
-- name    : FiniteEnergyPlane.exists_disk_nondegenerate_no_connection
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:05:04.057371+00:00
-- url     : https://prove2.me/theorems/766ad253-1d4a-4e71-8e4d-1ab00da7d5f9
-- title:
--   Nearby disks with nondegenerate zeros and no leaf joining two hyperbolic zeros
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level. Let $e$ embed $B_\rho$, $\rho>1$, into $S$, and let $1<r<\rho$. Let $U$ be open with closure in $B_r$, and suppose the characteristic field of $e$ has no zero on the frontier of $U$. For every $k$ and $\varepsilon>0$ there is a smooth $e'$ that embeds $B_r$ into $S$ such that
--
--   1. $e'=e$ near every point off $U$, and all derivatives of $e'-e$ of order at most $k$ are bounded by $\varepsilon$;
--   2. every zero in $U$ of the characteristic field of $e'$ is nondegenerate;
--   3. no leaf of $e'$ contained in $U$ goes from a hyperbolic zero in $U$ to a hyperbolic zero in $U$, equal or not.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$. Properties 2 and 3 belong to the Morse–Smale property of characteristic foliations; they hold for embedded disks in any strictly star-shaped level.
--
--   **Formalization Note** Zeros, leaves and spanning disks are those of `FiniteEnergyPlane_DiskFoliation`; the characteristic field $V$ is `charField e`. The disk is embedded on the open disk of radius $\rho$, and the new one on the smaller disk of radius $r$. The source states the full Morse–Smale property for closed surfaces in a contact $3$-manifold. The part of it stated here involves no closed leaves.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorem 42; E. Giroux, Convexité en topologie de contact, Comment. Math. Helv. 66 (1991), 637–677

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Theorem 42 (the part on zeros and connections of saddles). Let `e` embed the disk of radius `ρ` into
`S`, let `1 < r < ρ`, and let `U` be open with closure in the disk of radius `r` and no zero of the
characteristic field on its frontier. Arbitrarily `C^k`-close to `e` there is a disk `e'`, embedded on the disk
of radius `r` and equal to `e` near every point off `U`, whose zeros in `U` are nondegenerate, such that no nonconstant leaf in
`U` joins two hyperbolic zeros in `U` (equal or not). -/
theorem exists_disk_nondegenerate_no_connection (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (r : ℝ) (hr : 1 < r) (hrρ : r < ρ)
    (U : Set ℂ) (hU : IsOpen U) (hUr : closure U ⊆ ball 0 r)
    (hfr : ∀ z ∈ frontier U, charField e z ≠ 0) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ e' : ℂ → V 1, IsEmbeddedDisk H e' r ∧ (∀ z ∉ U, e' =ᶠ[𝓝 z] e) ∧
      (∀ m ≤ k, ∀ z, ‖iteratedFDeriv ℝ m (fun w => e' w - e w) z‖ ≤ ε) ∧
      (∀ z ∈ U, charField e' z = 0 → charDet e' z ≠ 0) ∧
      ∀ σ : ℝ → ℂ, IsCharCurve e' σ → Set.range σ ⊆ U → charField e' (σ 0) ≠ 0 →
        ∀ z₁ ∈ U, ∀ z₂ ∈ U, charField e' z₁ = 0 → charDet e' z₁ < 0 →
          charField e' z₂ = 0 → charDet e' z₂ < 0 →
          ¬ (Tendsto σ atBot (𝓝 z₁) ∧ Tendsto σ atTop (𝓝 z₂)) := by
  sorry

end FiniteEnergyPlane
