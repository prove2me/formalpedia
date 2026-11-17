-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_cylBounds_tubeMap
-- name    : FiniteEnergyPlane.exists_cylBounds_tubeMap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T23:55:09.53981+00:00
-- url     : https://prove2.me/theorems/f8c60809-122a-48e5-a17e-17284c8a27b2
-- title:
--   Cylindrical bounds for a tube around a plane in symplectization coordinates
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level, $P = (x, T)$ a periodic Reeb orbit, $M(t)$ a unitary frame of $\xi$ along $P$ (for some $J$), $\pi$ the radial projection to $S$ and $a$ the symplectization coordinate. Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ and $N : \mathbb{C} \to \mathrm{Hom}_{\mathbb{R}}(\mathbb{C}, \mathbb{R}^4)$ be smooth with $(\Delta, \nu) \mapsto Du(z)\Delta + N(z)\nu$ injective for every $z$, and suppose that in the coordinates $z = e^{2\pi(s+it)}$ the functions $a(u) - Ts - d$, $\pi(u) - x(Tt)$ and $e^{-2(Ts+d)} N(e^{2\pi(s+it)})\nu - M(t)\nu$ (each $\nu$) decay like $e^{-bs}$ in $C^\infty$ as $s \to +\infty$, with $b > 0$. Let $\Phi(z, w) = u(z) + N(z) w$ and $F = (a \circ \Phi, \pi \circ \Phi)$, and write $|h|_\zeta = \frac{|h_1|}{1+|\zeta|} + |h_2|$ for $h = (h_1, h_2) \in \mathbb{C}^2$.
--
--   Then there are $\rho > 0$, $C$ and $c_1 > 0$ such that $\Phi \ne 0$ and $F$ is smooth on $\mathbb{C} \times B(0, \rho)$; for all $\zeta$ and $|w| \le \rho/2$,
--   $$|DF(\zeta, w) h| \le C |h|_\zeta, \qquad |D^2F(\zeta, w)(h, k)| \le C |h|_\zeta |k|_\zeta ;$$
--   and $c_1 |h|_\zeta \le |DF(\zeta, 0) h|$ for all $\zeta$ and $h$.
--
--   Role: uniform cylindrical-scale control of a tube around a plane asymptotic to $P$, in the coordinates of the symplectization; used for injectivity of the tube, graph representations of nearby planes in it, and their estimates.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\pi$ and $a$ are `proj H` and `aCoord H`; $F$ is written out as a lambda; the decay hypotheses use `ExpDecayCInfty` along `cylInf`, with `endA`, `endW`; `cToVec` identifies $\mathbb{C}$ with the frame's domain.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Cylindrical bounds for a tube around a plane, in symplectization coordinates. Let `u : ℂ → V 1`
be smooth and nonvanishing, `N` smooth with `(Δ, ν) ↦ Du(z) Δ + N z ν` injective at every `z`, `M`
a unitary frame of `ξ` along `P`, and suppose that in the coordinates `z = e^{2π(s+it)}` the
functions `aCoord (u) - T s - d`, `proj (u) - x(T t)` and `e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν`
decay like `e^{-bs}` in `C^∞` (`b > 0`). Let `F(z, w) = (aCoord (Φ(z, w)), proj (Φ(z, w)))` with
`Φ(z, w) = u z + N z w`. Then for some `ρ > 0`, `Φ ≠ 0` and `F` is smooth on `ℂ × ball 0 ρ`, the
first and second derivatives of `F` are bounded by a constant `C` in the cylindrical weight
`|h|_ζ = ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖` at all `(ζ, w)` with `‖w‖ ≤ ρ / 2`, and
`c₁ |h|_ζ ≤ ‖DF(ζ, 0) h‖` for some `c₁ > 0` and all `ζ, h`. -/
theorem exists_cylBounds_tubeMap (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ C c₁ : ℝ, 0 < c₁ ∧
      (∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => (aCoord H (u p.1 + N p.1 p.2), proj H (u p.1 + N p.1 p.2)))
        ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) (ρ / 2) →
        (∀ h : ℂ × ℂ, ‖fderiv ℝ (fun p : ℂ × ℂ =>
          (aCoord H (u p.1 + N p.1 p.2), proj H (u p.1 + N p.1 p.2))) (ζ, w) h‖ ≤
            C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) ∧
        ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ (fun p : ℂ × ℂ =>
          (aCoord H (u p.1 + N p.1 p.2), proj H (u p.1 + N p.1 p.2)))) (ζ, w) h k‖ ≤
            C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)) ∧
      ∀ (ζ : ℂ) (h : ℂ × ℂ), c₁ * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) ≤
        ‖fderiv ℝ (fun p : ℂ × ℂ =>
          (aCoord H (u p.1 + N p.1 p.2), proj H (u p.1 + N p.1 p.2))) (ζ, 0) h‖ := by
  sorry

end FiniteEnergyPlane
