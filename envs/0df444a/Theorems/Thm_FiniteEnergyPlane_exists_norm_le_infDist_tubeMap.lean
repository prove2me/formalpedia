-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_le_infDist_tubeMap
-- name    : FiniteEnergyPlane.exists_norm_le_infDist_tubeMap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:51:00.574716+00:00
-- url     : https://prove2.me/theorems/e165ada8-594d-4ec8-9d7d-dc85f91bcb5f
-- title:
--   Normal coordinates in a tube around a plane are controlled by distances to the orbit
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, $P = (x, T)$ a prime periodic Reeb orbit, $M(t)$ a unitary frame of $\xi$ along $P$, and $\pi$ the radial projection to $S$, $a$ the symplectization coordinate. Let $u : \mathbb{C} \to \mathbb{R}^4$ and $N(z) : \mathbb{C} \to \mathbb{R}^4$ (real linear) be such that, in the coordinates $z = e^{2\pi(s+it)}$, the functions $a(u) - Ts - d$, $\pi(u) - x(Tt)$ and $e^{-2(Ts+d)} N(e^{2\pi(s+it)})\nu - M(t)\nu$ (each $\nu \in \mathbb{C}$) decay like $e^{-bs}$ in $C^\infty$ as $s \to +\infty$, with $b > 0$, and $u(z) \ne 0$ for all $z$.
--
--   Then there are $r_0 > 0$, $C$ and $R$ such that for all $\zeta, w \in \mathbb{C}$ with $|\zeta| \ge R$ and $|w| \le r_0$, the point $u(\zeta) + N(\zeta) w$ is nonzero and
--   $$|w| \le C\Big(\operatorname{dist}\big(\pi(u(\zeta) + N(\zeta) w), x(\mathbb{R})\big) + \operatorname{dist}\big(\pi(u(\zeta)), x(\mathbb{R})\big)\Big).$$
--
--   Role: in a tube $\Phi(\zeta, w) = u(\zeta) + N(\zeta) w$ around a plane asymptotic to $P$, the normal coordinate is bounded by distances to the orbit; this turns decay rates of planes towards $P$ into decay rates of their normal coordinates in the tube.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\pi$ and $a$ are `proj H` and `aCoord H`, distance to the orbit is `infDist _ (Set.range P.x)`; the decay hypotheses use `ExpDecayCInfty` along `cylInf`, with `endA`, `endW`; `cToVec` identifies $\mathbb{C}$ with the frame's domain.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Normal coordinates in a tube around a plane are controlled by distances to the orbit. Let
`P` be a prime periodic Reeb orbit, `M` a unitary frame of `ξ` along `P`, and let
`u : ℂ → V 1 \ {0}` and `N z : ℂ →L[ℝ] V 1` be such that, in the coordinates
`z = e^{2π(s+it)}`, `aCoord (u) - T s - d`, `proj (u) - x(T t)` and
`e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν` decay like `e^{-bs}` in `C^∞`. Then there are
`r₀ > 0`, `C` and `R` such that for `|ζ| ≥ R` and `|w| ≤ r₀` the point `u ζ + N ζ w` is nonzero
and `|w| ≤ C (dist(proj (u ζ + N ζ w), P) + dist(proj (u ζ), P))`. -/
theorem exists_norm_le_infDist_tubeMap (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ r₀ > 0, ∃ C R : ℝ, ∀ ζ w : ℂ, R ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      u ζ + N ζ w ≠ 0 ∧
      ‖w‖ ≤ C * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)) := by
  sorry

end FiniteEnergyPlane
