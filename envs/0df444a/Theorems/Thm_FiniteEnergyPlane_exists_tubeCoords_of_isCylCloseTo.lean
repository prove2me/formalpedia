-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tubeCoords_of_isCylCloseTo
-- name    : FiniteEnergyPlane.exists_tubeCoords_of_isCylCloseTo
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T09:39:12.29544+00:00
-- url     : https://prove2.me/theorems/163a822b-9950-48c7-a661-381c1271587b
-- title:
--   Maps close to a plane in cylindrical scale are graphs in a thin tube
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, $P = (x, T)$ a periodic Reeb orbit, $M(t)$ a unitary frame of $\xi$ along $P$, $\pi$ the radial projection to $S$ and $a$ the symplectization coordinate. Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ be smooth and $N : \mathbb{C} \to \mathrm{Hom}_{\mathbb{R}}(\mathbb{C}, \mathbb{R}^4)$ smooth with $(\Delta, \nu) \mapsto Du(z)\Delta + N(z)\nu$ injective for every $z$, and suppose that in the coordinates $z = e^{2\pi(s+it)}$ the functions $a(u) - Ts - d$, $\pi(u) - x(Tt)$ and $e^{-2(Ts+d)} N(e^{2\pi(s+it)})\nu - M(t)\nu$ (each $\nu \in \mathbb{C}$) decay like $e^{-bs}$ in $C^\infty$, $b > 0$. Let $\Phi(z, w) = u(z) + N(z) w$ be nonvanishing with injective derivative on $\mathbb{C} \times B(0, \rho)$ and, for some $c > 0$ and all $(z,w), (z',w')$ there,
--   $$c\Big(\frac{|z - z'|}{1 + |z| + |z'|} + |w - w'|\Big) \le |a(\Phi(z,w)) - a(\Phi(z',w'))| + |\pi(\Phi(z,w)) - \pi(\Phi(z',w'))|.$$
--
--   Then there is $\varepsilon > 0$ with the following property. Let $f : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ be smooth with, for all $z$,
--   $$|a(f(z)) - a(u(z))| \le \varepsilon,\quad |\pi(f(z)) - \pi(u(z))| \le \varepsilon,\quad (1 + |z|)\big(\|D(a \circ f)(z) - D(a \circ u)(z)\| + \|D(\pi \circ f)(z) - D(\pi \circ u)(z)\|\big) \le \varepsilon.$$
--   Then $f(z) = \Phi(\psi(z), v(z))$ for all $z$, where $\psi : \mathbb{C} \to \mathbb{C}$ is a homeomorphism, smooth with smooth inverse, and $v : \mathbb{C} \to \mathbb{C}$ is smooth, with $|v| \le \rho/2$, $\|D\psi - \mathrm{id}\| \le 1/2$ and $(1 + |z|)\|Dv(z)\| \le 1$ everywhere.
--
--   Role: planes close to $u$ in cylindrical scale are graphs over $u$ in the tube $\Phi$, with a reparametrization close to the identity; these coordinates are the input for comparing nearby planes.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\pi$ and $a$ are `proj H` and `aCoord H`; the closeness condition is `IsCylCloseTo H ε f u`; the decay hypotheses use `ExpDecayCInfty` along `cylInf` with `endA`, `endW`; `cToVec` identifies $\mathbb{C}$ with the frame's domain; the hypotheses $\mathrm{hH}, \mathrm{hJ}$ fix the setting.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a smooth nonvanishing plane, `N` a smooth normal
map with `(Δ, ν) ↦ Du(z) Δ + N z ν` injective, `C^∞` exponential decay of `aCoord (u) - T s - d`,
`proj (u) - x(T t)` and `e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν` for a unitary frame `M` of `ξ`
along `P`, and let the tube map
`Φ(z, w) = u z + N z w` be nonvanishing with injective derivative on `ℂ × ball 0 ρ` and satisfy there
the weighted two-point bound `hlow` with constant `c > 0`. Then there is `ε > 0` such that every smooth
nonvanishing `f : ℂ → V 1` that is `ε`-close to `u` in the sense of `IsCylCloseTo` can be written
as `f = Φ(ψ, v)` with `ψ` a homeomorphism of `ℂ`, smooth with smooth inverse, `v` smooth with
`‖v‖ ≤ ρ / 2`, `‖Dψ - id‖ ≤ 1/2` and `(1 + ‖z‖) ‖Dv(z)‖ ≤ 1` everywhere. -/
theorem exists_tubeCoords_of_isCylCloseTo (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖) :
    ∃ ε > 0, ∀ f : ℂ → V 1, ContDiff ℝ ∞ f → (∀ z, f z ≠ 0) → IsCylCloseTo H ε f u →
      ∃ (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ), ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ.symm ∧ ContDiff ℝ ∞ v ∧
        (∀ z, ‖v z‖ ≤ ρ / 2) ∧ (∀ z, f z = u (ψ z) + N (ψ z) (v z)) ∧
        (∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) ∧
        (∀ z, (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ 1) := by
  sorry

end FiniteEnergyPlane
