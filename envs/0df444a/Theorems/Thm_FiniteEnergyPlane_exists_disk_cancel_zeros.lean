-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_disk_cancel_zeros
-- name    : FiniteEnergyPlane.exists_disk_cancel_zeros
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:07:03.488418+00:00
-- url     : https://prove2.me/theorems/b440319a-8844-4bc9-8251-38b29488ff4f
-- title:
--   A disk without two given zeros of the same sign joined by a leaf
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level. Let $e$ embed $B_\rho$, $\rho>1$, into $S$, and let $1<r<\rho$. Let $z_1$ be a nicely elliptic zero and $z_2$ a hyperbolic zero of the characteristic field of $e$, of the same sign, joined by a leaf, and let $U$ be open, with closure in $B_r$, containing $z_1$, $z_2$ and the leaf. There is a smooth $e'$ that embeds $B_r$ into $S$, equals $e$ near every point off $U$, and whose characteristic field $V'$ satisfies
--   $$\{z\in U: V'(z)=0\}=\{z\in U: V(z)=0\}\setminus\{z_1,z_2\},$$
--   where $V$ is the characteristic field of $e$.
--
--   Here $B_\rho$ is the open disk of radius $\rho$ about $0$. This is the elimination lemma of Giroux, Eliashberg and Fuchs, for disks in strictly star-shaped levels.
--
--   **Formalization Note** Zeros, leaves and spanning disks are those of `FiniteEnergyPlane_DiskFoliation`; the characteristic field $V$ is `charField e`. The disk is embedded on the open disk of radius $\rho$, and the new one on the smaller disk of radius $r$. The leaf runs from $z_1$ to $z_2$ or from $z_2$ to $z_1$. The source also states that the area is unchanged; this is not asserted.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Proposition 43; E. Giroux, Convexité en topologie de contact, Comment. Math. Helv. 66 (1991), 637–677

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Proposition 43 (Giroux's elimination lemma). Let `e` embed the disk of radius `ρ` into `S`, and let
`1 < r < ρ`. Let `z₁` be a nicely elliptic and `z₂` a hyperbolic zero of the same sign, joined by a leaf, and let `U` be
open, with closure in the disk of radius `r`, containing the leaf, `z₁` and `z₂`. There is a disk `e'`,
embedded on the disk of radius `r` and equal to `e` near every point off `U`, whose zeros in `U` are those of `e` other than `z₁` and
`z₂`. -/
theorem exists_disk_cancel_zeros (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (e : ℂ → V 1) (ρ : ℝ) (he : IsEmbeddedDisk H e ρ) (r : ℝ) (hr : 1 < r) (hrρ : r < ρ)
    (U : Set ℂ) (hU : IsOpen U) (hUr : closure U ⊆ ball 0 r) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ U) (hz₂ : z₂ ∈ U)
    (h₁ : IsNicelyEllipticZero e z₁) (h₂ : charField e z₂ = 0) (h₂' : charDet e z₂ < 0)
    (hsign : 0 < charTrace e z₁ * charTrace e z₂) (σ : ℝ → ℂ) (hσ : IsCharCurve e σ)
    (hσU : Set.range σ ⊆ U)
    (hσ' : (Tendsto σ atBot (𝓝 z₁) ∧ Tendsto σ atTop (𝓝 z₂)) ∨
      (Tendsto σ atBot (𝓝 z₂) ∧ Tendsto σ atTop (𝓝 z₁))) :
    ∃ e' : ℂ → V 1, IsEmbeddedDisk H e' r ∧ (∀ z ∉ U, e' =ᶠ[𝓝 z] e) ∧
      ∀ z ∈ U, charField e' z = 0 ↔ charField e z = 0 ∧ z ≠ z₁ ∧ z ≠ z₂ := by
  sorry

end FiniteEnergyPlane
