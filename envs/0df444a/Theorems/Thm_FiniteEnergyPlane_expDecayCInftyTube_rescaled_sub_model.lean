-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_sub_model
-- name    : FiniteEnergyPlane.expDecayCInftyTube_rescaled_sub_model
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-15T17:46:21.131207+00:00
-- url     : https://prove2.me/theorems/df353fef-d684-4e84-b9a9-6deafa3ac82f
-- title:
--   The rescaled tube map along a plane end converges to its model exponentially in C-infinity
-- statement:
--   Let $S=H^{-1}(1)$ be strictly star-shaped, $P=(x,T)$ a periodic Reeb orbit, and write $z=e^{2\pi(s+it)}$. Let $u:\mathbb C\to\mathbb R^4\setminus\{0\}$ be such that $a(u(z))-Ts-d$ and $\mathrm{proj}(u(z))-x(Tt)$ decay like $e^{-bs}$ in $C^\infty$ ($b>0$), where $u=e^{2a}\,\mathrm{proj}(u)$. Let $N(z):\mathbb C\to\mathbb R^4$ be real linear and $M(t):\mathbb R^2\to\mathbb R^4$ a loop of linear maps such that $e^{-2(Ts+d)}N(z)\nu-M(t)\nu$ decays like $e^{-bs}$ in $C^\infty$ for every $\nu\in\mathbb C=\mathbb R^2$.
--
--   Then for every $\rho>0$ the map
--   $$(s,t,w)\mapsto e^{-2(Ts+d)}\bigl(u(z)+N(z)w\bigr)-\bigl(x(Tt)+M(t)w\bigr)$$
--   decays like $e^{-bs}$ in $C^\infty$ as $s\to+\infty$, uniformly in $t\in\mathbb R$ and $|w|<\rho$.
--
--   This identifies the asymptotic shape of the tube $\Phi(z,w)=u(z)+N(z)w$ around the end of $u$, after removing the radial growth, as the model $x(Tt)+M(t)w$.
--
--   Formalization Note: $\mathbb C\cong\mathbb R^2$ via `cToVec`; $a$ and $\mathrm{proj}$ are `aCoord H`, `proj H` (through `endA`, `endW` along `cylInf`); tube decay is `ExpDecayCInftyTube _ ρ b`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The rescaled tube map converges to its model on the tube. Let `u : ℂ → V 1 \ {0}` with
`aCoord (u) - T s - d` and `proj (u) - x(T t)` decaying like `e^{-bs}` in `C^∞` in the coordinates
`z = e^{2π(s+it)}`, and let `N z : ℂ →L[ℝ] V 1` and a loop `M` with
`e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t)(cToVec ν)` decaying like `e^{-bs}` in `C^∞` for every `ν`.
Then for every `ρ > 0`, `e^{-2(Ts+d)} (u(z) + N(z) w) - (x(T t) + M(t)(cToVec w))` decays like
`e^{-bs}` in `C^∞` on the tube, uniformly in `t` and `w ∈ ball 0 ρ`. -/
theorem expDecayCInftyTube_rescaled_sub_model (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      Real.exp (-(2 * (P.T * q.1 + d))) •
          (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) -
        (P.x (P.T * q.2.1) + M q.2.1 (cToVec q.2.2))) ρ b := by
  sorry

end FiniteEnergyPlane
