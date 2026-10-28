-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_add_smul
-- name    : FiniteEnergyPlane.isJHolomorphicOn_comp_add_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T21:03:48.964625+00:00
-- url     : https://prove2.me/theorems/459f0f5b-7bf8-4bba-8c56-2318dd1d6249
-- title:
--   Real affine reparametrisations preserve pseudoholomorphic maps
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $J:E\to\mathrm{End}_{\mathbb R}(E)$ any map, $U\subseteq\mathbb{C}$ and $u:\mathbb{C}\to E$ a map that is $J$-holomorphic on $U$, i.e. differentiable at each $z\in U$ with $\partial_s u+J(u)\,\partial_t u=0$ there. For $c\in\mathbb{C}$ and $a\in\mathbb{R}$ the map $v(w)=u(c+aw)$ is $J$-holomorphic on $\{w : c+aw\in U\}$, and
--   $$Dv(w)=a\,Du(c+aw)\qquad\text{whenever } c+aw\in U .$$
--
--   This is the rescaling step used in bubbling-off and removable-singularity arguments, where a map is reparametrised on a small disc around a point of large derivative.
--
--   **Formalization Note** `J`-holomorphicity is `JHolomorphic.IsJHolomorphicOn` (pointwise differentiability and `dbarJ J u z = 0`). The derivative identity is stated for `fderiv ℝ` as an equality of continuous real-linear maps `ℂ →L[ℝ] E`.
-- source:
--   Standard; used for rescaling in C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 9

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Real affine reparametrisations of the domain preserve `J`-holomorphicity. If `u` is
`J`-holomorphic on `U ⊆ ℂ`, `c ∈ ℂ` and `a ∈ ℝ`, then `w ↦ u (c + a w)` is `J`-holomorphic on
`{w | c + a w ∈ U}`, and its derivative there is `a • Du(c + a w)`. -/
theorem isJHolomorphicOn_comp_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (U : Set ℂ) (u : ℂ → E)
    (hhol : JHolomorphic.IsJHolomorphicOn J U u) (c : ℂ) (a : ℝ) :
    JHolomorphic.IsJHolomorphicOn J {w | c + a • w ∈ U} (fun w => u (c + a • w)) ∧
      ∀ w : ℂ, c + a • w ∈ U →
        fderiv ℝ (fun w => u (c + a • w)) w = a • fderiv ℝ u (c + a • w) := by
  sorry

end FiniteEnergyPlane
