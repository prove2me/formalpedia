-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousOn_fderiv_slice
-- name    : FiniteEnergyPlane.continuousOn_fderiv_slice
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:38:57.057302+00:00
-- url     : https://prove2.me/theorems/da00f363-3441-49aa-81cd-b743bc79f51c
-- title:
--   Joint continuity of the slice derivatives of a C^1 map on I × ℂ
-- statement:
--   Let $F$ be a real normed space, $I\subseteq\mathbb{R}$ open, and $W:\mathbb{R}\times\mathbb{C}\to F$ of class $C^1$ on $I\times\mathbb{C}$. Then the derivative of the slices,
--   $$(t,z)\mapsto D\big(W(t,\cdot)\big)(z)\in\mathcal{L}_{\mathbb{R}}(\mathbb{C},F),$$
--   is continuous on $I\times\mathbb{C}$.
--
--   The derivatives of the individual slices of a $C^1$ family depend continuously on the parameter. It is used for convergence of the slices of families of planes (Hryniewicz 2012, Section 7).
--
--   **Formalization Note** The slice derivative is `fderiv ℝ (fun z => W (p.1, z)) p.2`; $\mathbb{C}$ is a real normed space.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `W` is `C¹` on `I × ℂ` with `I` open, then `(t, z) ↦ D(W(t, ·))(z)` is continuous on
`I × ℂ`. -/
theorem continuousOn_fderiv_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : ℝ × ℂ → F) (I : Set ℝ) (hI : IsOpen I) (hW : ContDiffOn ℝ 1 W (I ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × ℂ => fderiv ℝ (fun z => W (p.1, z)) p.2) (I ×ˢ Set.univ) := by
  sorry

end FiniteEnergyPlane
