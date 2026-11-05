-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_loop_near_orbit_of_mem_fastPlaneSet
-- name    : FiniteEnergyPlane.exists_loop_near_orbit_of_mem_fastPlaneSet
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T21:12:54.522655+00:00
-- url     : https://prove2.me/theorems/1677f9d8-050c-45e3-b0b8-d7384deca590
-- title:
--   Uniform closeness of large circles of fast planes to the asymptotic orbit
-- statement:
--   Let $P=(x,T)$ be a periodic Reeb orbit on a strictly star-shaped level $S\subset\mathbb{R}^4$ such that every periodic orbit of period at most $T$ is nondegenerate, and let $0<\gamma$ be smaller than every such period and every difference of two distinct such periods. For every $\varepsilon>0$ there is a radius $\rho_0$ such that, for every plane $u$ in the set $\Theta(K,P)$ of fast finite-energy planes asymptotic to $P$ at $\infty$ with $u(0)\in K$ and $d\lambda$-energy $\gamma$ outside the closed unit disk, and every $\rho\ge\rho_0$, the loop $t\mapsto\mathrm{pr}(u(\rho e^{2\pi it}))$ is uniformly $\varepsilon$-close to $t\mapsto x(Tt+c)$ for some phase $c$.
--
--   The radius does not depend on $u$ or on $K$. This is the uniform control at $\infty$ used for sequences of such planes.
--
--   **Formalization Note** $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$ is `V 1 \ {0}`, with $a$ = `aCoord H` and $\mathrm{pr}$ = `proj H`; $\Theta$ = `fastPlaneSet H J P K γ`. The loop is `loopInS H u (ccwLoop ρ)`. The phase $c$ may depend on $u$ and $\rho$.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4 (Lemma 4.17 and its proof)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` be a periodic Reeb orbit on `S ⊂ ℝ⁴` such that every periodic orbit of period at most
`P.T` is nondegenerate, and let `0 < γ` be smaller than every such period and every difference of two
distinct such periods. For every `ε > 0` there is a radius `ρ₀`, independent of the plane, such that
for every `u ∈ fastPlaneSet H J P K γ` and every `ρ ≥ ρ₀` the loop `t ↦ proj(u(ρ e^{2πit}))` is
uniformly `ε`-close to `t ↦ P.x(P.T t + c)` for some phase `c`. -/
theorem exists_loop_near_orbit_of_mem_fastPlaneSet (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (γ : ℝ) (hγ : 0 < γ) (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (hγ₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|)
    (K : Set (V 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ u ∈ fastPlaneSet H J P K γ, ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ c : ℝ, ∀ t : ℝ, ‖loopInS H u (ccwLoop ρ) t - P.x (P.T * t + c)‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
