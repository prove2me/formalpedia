-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_le_tubeMap_of_mul_le
-- name    : FiniteEnergyPlane.exists_mul_le_tubeMap_of_mul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T23:46:59.887678+00:00
-- url     : https://prove2.me/theorems/0eb6038f-2a8e-40b2-9c01-77f989c3b0c0
-- title:
--   The weighted lower bound of a plane extends to a thin tube around it
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, $P = (x, T)$ a periodic Reeb orbit, $M(t)$ a unitary frame of $\xi$ along $P$, $\pi$ the radial projection to $S$ and $a$ the symplectization coordinate. Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ be smooth with, for some $c_0 > 0$ and all $z, z'$,
--   $$c_0 |z - z'| \le (1 + |z| + |z'|)\big(|a(u(z)) - a(u(z'))| + |\pi(u(z)) - \pi(u(z'))|\big).$$
--   Let $N : \mathbb{C} \to \mathrm{Hom}_{\mathbb{R}}(\mathbb{C}, \mathbb{R}^4)$ be smooth with $(\Delta, \nu) \mapsto Du(z)\Delta + N(z)\nu$ injective for every $z$, and suppose that in the coordinates $z = e^{2\pi(s+it)}$ the functions $a(u) - Ts - d$, $\pi(u) - x(Tt)$ and $e^{-2(Ts+d)} N(e^{2\pi(s+it)})\nu - M(t)\nu$ (each $\nu \in \mathbb{C}$) decay like $e^{-bs}$ in $C^\infty$ as $s \to +\infty$, with $b > 0$.
--
--   Then, with $\Phi(z, w) = u(z) + N(z) w$, there are $\rho > 0$ and $c > 0$ such that for all $(z, w), (z', w')$ with $|w|, |w'| < \rho$,
--   $$c\Big(\frac{|z - z'|}{1 + |z| + |z'|} + |w - w'|\Big) \le |a(\Phi(z,w)) - a(\Phi(z',w'))| + |\pi(\Phi(z,w)) - \pi(\Phi(z',w'))| .$$
--
--   Role: the weighted lower bound of an embedded plane, uniform in cylindrical scale, extends to a thin tube $\Phi$ around it; in particular $\Phi$ is injective on $\mathbb{C} \times B(0, \rho)$, with constants usable for nearby planes.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\pi$ and $a$ are `proj H` and `aCoord H`; the decay hypotheses use `ExpDecayCInfty` along `cylInf`, with `endA`, `endW`; `cToVec` identifies $\mathbb{C}$ with the frame's domain; the hypotheses $\mathrm{hH}, \mathrm{hJ}$ fix the setting.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The weighted lower bound of a plane extends to a thin tube around it. Let `u : ℂ → V 1`
be smooth and nonvanishing with `c₀ ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) (|Δ aCoord| + ‖Δ proj‖)` for
the values of `u` at all `z, z'`, and suppose that in the coordinates `z = e^{2π(s+it)}` the
functions `aCoord (u) - T s - d`, `proj (u) - x(T t)` and
`e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν` decay like `e^{-bs}` in `C^∞` (`b > 0`), where `N` is
smooth, `(Δ, ν) ↦ Du(z) Δ + N z ν` is injective at every `z`, and `M` is a unitary frame of `ξ`
along `P`. Then the tube map `Φ(z, w) = u z + N z w` satisfies, for some `ρ > 0`, `c > 0` and all
`p, q ∈ ℂ × ball 0 ρ`, `c (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
|aCoord (Φ p) - aCoord (Φ q)| + ‖proj (Φ p) - proj (Φ q)‖`. -/
theorem exists_mul_le_tubeMap_of_mul_le (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hslice : ∀ z z' : ℂ, c₀ * ‖z - z'‖ ≤ (1 + ‖z‖ + ‖z'‖) *
      (|aCoord H (u z) - aCoord H (u z')| + ‖proj H (u z) - proj H (u z')‖)) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ c > 0, ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖ := by
  sorry

end FiniteEnergyPlane
