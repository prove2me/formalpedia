-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_disk_liouville_eq_add
-- name    : FiniteEnergyPlane.exists_disk_liouville_eq_add
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:04:27.108261+00:00
-- url     : https://prove2.me/theorems/c7e77b26-4b5c-4771-b579-8948eb3f6f87
-- title:
--   Disks whose pulled-back contact form differs by a small exact form
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level. Let $e$ embed $B_\rho$, $\rho>1$, into $S$, and let $1<r<\rho$. There is $\varepsilon>0$ such that for every smooth $h:\mathbb{C}\to\mathbb{R}$ with compact support in $B_r$ and $|dh|\le\varepsilon$ there is a smooth $e'$ that embeds $B_r$ into $S$, equals $e$ off the support of $h$, and satisfies
--   $$e'^*\lambda_0=e^*\lambda_0+dh\qquad\text{on }B_r .$$
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$. In particular $e'^*\omega_0=e^*\omega_0$ on $B_r$. The statement describes a class of disks with prescribed pulled-back contact form; it holds for every embedded disk.
--
--   **Formalization Note** The disk is embedded on the open disk of radius $\rho$, and the new one on the smaller disk of radius $r$. The constant $\varepsilon$ depends on $e$, $\rho$ and $r$ only. The statement is implicit in the deformations of disks in the sources and is not numbered there.
-- source:
--   cf. H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, Section 3; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Section 5

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1999, tight sphere II), § 3. Let `e` embed the disk of radius `ρ` into `S`, and let
`1 < r < ρ`. There is `ε > 0` such that for every smooth `h` with compact support in the disk of radius `r`
and `|dh| ≤ ε` there is a disk `e'` in `S`, embedded on the disk of radius `r` and equal to `e` off the support of
`h`, with `e'*λ₀ = e*λ₀ + dh` on the disk of radius `r`. -/
theorem exists_disk_liouville_eq_add (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (r : ℝ) (hr : 1 < r) (hrρ : r < ρ) :
    ∃ ε > 0, ∀ h : ℂ → ℝ, ContDiff ℝ ∞ h → tsupport h ⊆ ball 0 r → (∀ z, ‖fderiv ℝ h z‖ ≤ ε) →
      ∃ e' : ℂ → V 1, IsEmbeddedDisk H e' r ∧ (∀ z ∉ tsupport h, e' z = e z) ∧
        ∀ z ∈ ball (0 : ℂ) r, ∀ w : ℂ, liouville (e' z) (fderiv ℝ e' z w) =
          liouville (e z) (fderiv ℝ e z w) + fderiv ℝ h z w := by
  sorry

end FiniteEnergyPlane
