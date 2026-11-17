-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_aCoord_proj_model_of_tubeMap
-- name    : FiniteEnergyPlane.exists_aCoord_proj_model_of_tubeMap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T18:03:37.177845+00:00
-- url     : https://prove2.me/theorems/6b380cfd-856e-459d-9913-173ac399a3bb
-- title:
--   Asymptotics of the symplectization coordinates on a tube around a plane
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level, $P = (x, T)$ a periodic Reeb orbit on $S$ and $M(t)$ a unitary frame of $\xi$ along $P$. Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ and $N(z) : \mathbb{C} \to \mathbb{R}^4$ (real linear) be such that, in the coordinates $z = e^{2\pi(s+it)}$, the functions $a(u) - Ts - d$, $\pi(u) - x(Tt)$ and $e^{-2(Ts+d)} N(e^{2\pi(s+it)})\nu - M(t)\nu$ (for each $\nu \in \mathbb{C}$) decay like $e^{-bs}$ in $C^\infty$, where $b > 0$ and $a$, $\pi$ are the symplectization coordinate and the radial projection to $S$.
--
--   Put $\Phi(z, w) = u(z) + N(z) w$ and let $\rho > 0$ be such that $x(Tt) + M(t) w \neq 0$ for $|w| \le \rho$ and $\Phi \neq 0$ on $\mathbb{C} \times B_\rho(0)$. Then there are smooth functions $\alpha(t, w)$ and $X(t, w)$ on $\mathbb{R} \times B_\rho(0)$, $1$-periodic in $t$, with $\alpha(t, 0) = 0$ and $X(t, 0) = x(Tt)$, such that
--   $$a(\Phi(e^{2\pi(s+it)}, w)) - Ts - d - \alpha(t, w) \quad\text{and}\quad \pi(\Phi(e^{2\pi(s+it)}, w)) - X(t, w)$$
--   decay like $e^{-bs}$ in $C^\infty$ as $s \to +\infty$, uniformly in $t \in \mathbb{R}$ and $w \in B_\rho(0)$.
--
--   Role: this gives the cylindrical model of the symplectization coordinates of a tube around a finite-energy plane, which is one clause of a standard tube structure.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`; $a$ and $\pi$ are `aCoord H` and `proj H`; $M(t)$ acts on `cToVec w`; the decay notions are `ExpDecayCInfty` (on the end) and `ExpDecayCInftyTube` (on the tube).
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Asymptotics of the symplectization coordinates on a tube. Let `u`, `N`, `M` be as for a
standard tube: `aCoord (u) - T s - d`, `proj (u) - x(T t)` and
`e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν` decay like `e^{-bs}` in `C^∞`. Put
`Φ(z, w) = u z + N z w` and assume `x(T t) + M(t)(cToVec w) ≠ 0` for `|w| ≤ ρ` and `Φ ≠ 0` on
`ℂ × ball 0 ρ`. Then there are smooth `1`-periodic `α`, `X` on `ℝ × ball 0 ρ` with
`α(t, 0) = 0`, `X(t, 0) = x(T t)` such that `aCoord (Φ) - T s - d - α(t, w)` and
`proj (Φ) - X(t, w)` decay like `e^{-bs}` in `C^∞`, uniformly in `t` and `w ∈ ball 0 ρ`. -/
theorem exists_aCoord_proj_model_of_tubeMap (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hm : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → P.x (P.T * t) + M t (cToVec w) ≠ 0)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0) :
    ∃ (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
      ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
      (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t)) ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - P.T * q.1 - d -
          α (q.2.1, q.2.2)) ρ b ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - X (q.2.1, q.2.2)) ρ b := by
  sorry

end FiniteEnergyPlane
