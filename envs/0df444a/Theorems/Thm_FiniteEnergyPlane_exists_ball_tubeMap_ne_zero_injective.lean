-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_ball_tubeMap_ne_zero_injective
-- name    : FiniteEnergyPlane.exists_ball_tubeMap_ne_zero_injective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T10:59:51.047501+00:00
-- url     : https://prove2.me/theorems/7375d7a8-3d61-4497-88a0-0ca8fcef36de
-- title:
--   The tube map around a plane with asymptotic normal frame is nonzero and immersive on a uniform tube
-- statement:
--   Let $S=H^{-1}(1)$ be strictly star-shaped, $P=(x,T)$ a periodic Reeb orbit, $J$ a complex structure on $\xi$, and write $z=e^{2\pi(s+it)}$. Let $u:\mathbb C\to\mathbb R^4\setminus\{0\}$ be smooth such that $a(u(z))-Ts-d$ and $\mathrm{proj}(u(z))-x(Tt)$ decay like $e^{-bs}$ in $C^\infty$ ($b>0$), where $u=e^{2a}\,\mathrm{proj}(u)$. Let $N(z):\mathbb C\to\mathbb R^4$ be real linear and smooth in $z$, with
--   $$(\Delta,\nu)\mapsto Du(z)\,\Delta+N(z)\,\nu\quad\text{injective for every }z\in\mathbb C,$$
--   and let $M$ be a unitary frame of $(\xi,J)$ along $P$ such that $e^{-2(Ts+d)}N(z)\nu-M(t)\nu$ decays like $e^{-bs}$ in $C^\infty$ for every $\nu\in\mathbb C=\mathbb R^2$.
--
--   Then there is $\rho>0$ such that the map $\Phi(z,w)=u(z)+N(z)\,w$ satisfies, for all $z\in\mathbb C$ and $|w|<\rho$,
--   $$\Phi(z,w)\neq0\qquad\text{and}\qquad D\Phi(z,w)\ \text{is injective}.$$
--
--   So $\Phi$ is an immersion of the uniform tube $\mathbb C\times\{|w|<\rho\}$ into $\mathbb R^4\setminus\{0\}$ around the plane $u$.
--
--   Formalization Note: $\mathbb C\cong\mathbb R^2$ via `cToVec`; $a$ and $\mathrm{proj}$ are `aCoord H`, `proj H` (through `endA`, `endW` along `cylInf`); the unitary frame is `IsUnitaryXiFrame J P M`; derivatives are `fderiv ℝ`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Nondegeneracy of the tube map on a uniform tube. Let `u : ℂ → V 1 \ {0}` be smooth, with
`aCoord (u) - T s - d` and `proj (u) - x(T t)` decaying like `e^{-bs}` in `C^∞` in the
coordinates `z = e^{2π(s+it)}`. Let `N z : ℂ →L[ℝ] V 1` be smooth with
`(Δ, ν) ↦ Du(z) Δ + N z ν` injective for every `z`, and let `M` be a unitary frame of `ξ` along
`P` such that `e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν` decays like `e^{-bs}` in `C^∞`. Then the
map `Φ(z, w) = u z + N z w` is nonzero and has injective derivative on `ℂ × ball 0 ρ` for some
`ρ > 0`. -/
theorem exists_ball_tubeMap_ne_zero_injective (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) := by
  sorry

end FiniteEnergyPlane
