-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_fderiv_ne_zero_of_isCompact_fiber
-- name    : FiniteEnergyPlane.exists_fderiv_ne_zero_of_isCompact_fiber
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:06:29.865839+00:00
-- url     : https://prove2.me/theorems/c43ac741-871d-4c37-a986-76aab1e9e784
-- title:
--   A differentiable map on an open subset of $\mathbb{C}$ with a compact fibre has nonzero derivative at points with values arbitrarily close to that fibre value
-- statement:
--   Let $F$ be a real normed space, $U\subseteq\mathbb{C}$ open and $u:\mathbb{C}\to F$ real-differentiable on $U$. Let $p\in u(U)$ and assume that the fibre $U\cap u^{-1}(p)$ is compact. Then for every $\varepsilon>0$ there is $z\in U$ with
--   $$\|u(z)-p\|<\varepsilon\qquad\text{and}\qquad Du(z)\neq 0 .$$
--
--   This holds for every map that is proper onto a neighbourhood of $p$ (for example a proper map of $U$ into a ball around $p$), so such maps have regular points with values arbitrarily close to $p$.
--
--   **Formalization Note** Differentiability is `DifferentiableOn ℝ u U`, the fibre hypothesis is `IsCompact (U ∩ u ⁻¹' {p})`, and $Du(z)$ is `fderiv ℝ u z`.
-- source:
--   Standard; used for the monotonicity lemma, A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, p. 152

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Clopen

namespace FiniteEnergyPlane

open Metric Filter Topology

/-- Let `u` be differentiable on an open set `U ⊆ ℂ` and let `p ∈ u(U)` have compact fibre
`U ∩ u⁻¹(p)`. Then every neighbourhood `B_ε(p)` contains a value `u(z)`, `z ∈ U`, at which the
derivative of `u` is nonzero. -/
theorem exists_fderiv_ne_zero_of_isCompact_fiber {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F} (hu : DifferentiableOn ℝ u U)
    {p : F} (hp : p ∈ u '' U) (hK : IsCompact (U ∩ u ⁻¹' {p})) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ U, ‖u z - p‖ < ε ∧ fderiv ℝ u z ≠ 0 := by
  sorry

end FiniteEnergyPlane
