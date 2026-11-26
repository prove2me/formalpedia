-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_closedLeafDisk
-- name    : FiniteEnergyPlane.exists_closedLeafDisk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:08:49.820776+00:00
-- url     : https://prove2.me/theorems/d8f47eae-7e70-5afd-8ffd-39c287efbd8a
-- title:
--   Closed leaves around a single zero
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level. Let $e$ immerse $B_\rho$, $\rho>1$, into $S$, let $1<r<\rho$, and suppose the characteristic field of $e$ has a closed leaf in $B_r$. Let $O\subset\mathbb{R}^4$ be an open neighbourhood of $e(\overline{B_r})$. There is a smooth $e'$ that immerses $B_r$ into $S\cap O$ and whose characteristic foliation has a closed leaf $\sigma'$ in $B_r$ bounding a domain $\Omega$ such that
--
--   1. $\Omega$ contains exactly one zero, which is positive and nicely elliptic;
--   2. $\Omega$ contains no closed leaf.
--
--   If $e$ is injective on $B_\rho$, then $e'$ can be taken injective on $B_r$.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$. The statement concerns closed leaves of immersed disks; nothing is asserted about the position of $\sigma'$ relative to the given leaf.
--
--   **Formalization Note** The domain is `IsClosedLeafDisk`. The sources treat embedded disks. Closed leaves of immersed disks are allowed here, so the hypotheses are not those of an embedded disk, which by `charField_eq_zero_of_periodic` has no closed leaf.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, pp. 1149–1151; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorems 44 and 45

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1999, tight sphere II), pp. 1149–1151; Hofer (1993), Theorems 44 and 45. Let `e` immerse the
disk of radius `ρ` into `S`, let `1 < r < ρ`, and suppose that the characteristic field of `e` has a closed leaf in
the disk of radius `r`. In every neighbourhood of the image of the closed disk of radius `r` there is an immersed disk
with a closed leaf that bounds a domain containing exactly one zero, positive and nicely elliptic, and no closed
leaf. If `e` is injective on the disk of radius `ρ`, then the new disk can be taken to be embedded. -/
theorem exists_closedLeafDisk (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsImmersedDisk H e ρ) (r : ℝ) (hr : 1 < r) (hrρ : r < ρ)
    (σ : ℝ → ℂ) (T : ℝ) (hσ : IsPeriodicLeaf e σ T) (hσr : Set.range σ ⊆ ball 0 r)
    (O : Set (V 1)) (hO : IsOpen O) (heO : e '' closedBall 0 r ⊆ O) :
    ∃ e' : ℂ → V 1, IsImmersedDisk H e' r ∧ Set.MapsTo e' (ball 0 r) O ∧
      (Set.InjOn e (ball 0 ρ) → Set.InjOn e' (ball 0 r)) ∧
      ∃ (σ' : ℝ → ℂ) (T' : ℝ) (Ω : Set ℂ) (z₀ : ℂ), IsClosedLeafDisk e' r σ' T' Ω z₀ := by
  sorry

end FiniteEnergyPlane
