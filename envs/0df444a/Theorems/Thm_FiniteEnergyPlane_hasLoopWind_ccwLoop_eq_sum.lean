-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_eq_sum
-- name    : FiniteEnergyPlane.hasLoopWind_ccwLoop_eq_sum
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:22:05.92117+00:00
-- url     : https://prove2.me/theorems/a45c2205-4f56-44ca-acb5-c9310b03ff56
-- title:
--   Argument principle for continuous functions: the boundary winding is the sum of the local windings
-- statement:
--   Let $c\in\mathbb{C}$, $R>0$, and let $P\subset B(c,R)$ be a finite set of points in the open disc. Let $g$ be a complex function that is continuous and nowhere zero on $\overline{B}(c,R)\setminus P$. Suppose that for each $p\in P$ there are $m_p\in\mathbb{Z}$ and $r_p>0$ such that for every $0<\rho<r_p$ the loop $t\mapsto g(p+\rho e^{2\pi it})$ has winding number $m_p$. Then the loop $t\mapsto g(c+Re^{2\pi it})$ along the boundary circle has winding number
--   $$\sum_{p\in P} m_p .$$
--
--   No differentiability of $g$ is assumed. Applied to the $\xi$-component $\pi\partial_s u$ of a pseudoholomorphic curve, it relates the total index of its zeros and punctures inside a disc to its winding along the boundary.
--
--   **Formalization Note** $g$ is `g : ℂ → ℂ` with `ContinuousOn g (closedBall c R \ ↑P)` and `g z ≠ 0` there; `P : Finset ℂ`, `m : ℂ → ℤ`. The circles are `p + ccwLoop ρ t` with `ccwLoop ρ t = ρ e^{2πit}`, and "winding number $k$" is `HasLoopWind f k`.
-- source:
--   Standard (degree theory in the plane); used in U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 2.15, and H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric

/-- Argument principle for continuous functions. Let `P ⊂ B(c, R)` be finite and `g` continuous and
nowhere zero on `closedBall c R \ P`. Suppose that for each `p ∈ P`, `g` has winding number `m p`
along every counterclockwise circle `t ↦ p + ρ e^{2πit}` of small radius `ρ`. Then `g` has winding
number `∑_{p ∈ P} m p` along the boundary circle `t ↦ c + R e^{2πit}`. -/
theorem hasLoopWind_ccwLoop_eq_sum (g : ℂ → ℂ) (P : Finset ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hP : ∀ p ∈ P, p ∈ ball c R) (hg : ContinuousOn g (closedBall c R \ ↑P))
    (hg0 : ∀ z ∈ closedBall c R \ ↑P, g z ≠ 0) (m : ℂ → ℤ)
    (hm : ∀ p ∈ P, ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g (p + ccwLoop ρ t)) (m p)) :
    HasLoopWind (fun t => g (c + ccwLoop R t)) (∑ p ∈ P, m p) := by
  sorry

end FiniteEnergyPlane
