-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_comp_mul
-- name    : FiniteEnergyPlane.energy_comp_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T22:20:52.307937+00:00
-- url     : https://prove2.me/theorems/41efa85c-79f4-4bfb-8392-b1d360731913
-- title:
--   Hofer energy under complex scaling of the domain
-- statement:
--   Let $A\in\mathbb{C}\setminus\{0\}$ and let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ be such that its symplectization coordinates $a=\mathrm{aCoord}_H\circ u$ and $w=\mathrm{proj}_H\circ u$ are real differentiable. For every measurable $s\subseteq\mathbb{C}$, Hofer's energy of $z\mapsto u(Az)$ on $s$ equals Hofer's energy of $u$ on $A\cdot s$.
--
--   Reusable whenever a finite-energy curve is rotated or rescaled in the domain.
--
--   **Formalization Note** Hofer's energy is `energy H s u`, a supremum over admissible functions with values in $[0,\infty]$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `A ∈ ℂ` be nonzero and let `u : ℂ → V n` be such that `aCoord H ∘ u` and `proj H ∘ u` are
differentiable. For every measurable `s ⊆ ℂ`, Hofer's energy of `z ↦ u (A z)` on `s` equals Hofer's
energy of `u` on the image `A · s`. -/
theorem energy_comp_mul {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (A : ℂ) (hA : A ≠ 0)
    (ha : Differentiable ℝ (fun y => aCoord H (u y)))
    (hw : Differentiable ℝ (fun y => proj H (u y))) (s : Set ℂ) (hs : MeasurableSet s) :
    energy H s (fun z => u (A * z)) = energy H ((fun y => A * y) '' s) u := by
  sorry

end FiniteEnergyPlane
