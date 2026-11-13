-- Prove2me | Theorems.Thm_FiniteEnergyPlane_cylJ_iteratedFDeriv_bdd
-- name    : FiniteEnergyPlane.cylJ_iteratedFDeriv_bdd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T22:38:02.699239+00:00
-- url     : https://prove2.me/theorems/d8e837ad-3ece-4f79-98b3-7540e372d147
-- title:
--   Derivative bounds of the cylinder form of a standard tube structure at $+\infty$
-- statement:
--   Let $\rho, b > 0$ and $(\bar J, J_\infty, S_\infty)$ a standard tube structure (`IsStdTubeStructure ρ b Jbar Jinf Sinf`). For every $m$ there are $C, s_1$ such that the $m$-th derivative of $(s, t, w) \mapsto$ `cylJ Jbar s t w` has norm at most $C$ at every $(s, t, w)$ with $s \ge s_1$, $t \in \mathbb{R}$, $|w| \le \rho/2$.
--
--   **Role.** Uniform control of the cylinder form of $\bar J$ near the end $s = +\infty$ of the plane.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Under a standard tube structure, every derivative of `(s, t, w) ↦ cylJ Jbar s t w` is bounded
on `[s₁, ∞) × ℝ × closedBall 0 (ρ/2)` for some `s₁`. -/
theorem cylJ_iteratedFDeriv_bdd (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) (m : ℕ) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ w ∈ closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDeriv ℝ m (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2) (s, t, w)‖ ≤ C := by
  sorry

end FiniteEnergyPlane
