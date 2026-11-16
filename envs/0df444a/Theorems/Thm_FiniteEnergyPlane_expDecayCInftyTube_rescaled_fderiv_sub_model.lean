-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_fderiv_sub_model
-- name    : FiniteEnergyPlane.expDecayCInftyTube_rescaled_fderiv_sub_model
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-15T18:03:33.531443+00:00
-- url     : https://prove2.me/theorems/577f7626-7530-413e-9c4e-3b8e7d1e272f
-- title:
--   The rescaled derivative of the tube map along a plane end converges to the model derivative exponentially in C-infinity
-- statement:
--   Let $S=H^{-1}(1)$ be strictly star-shaped, $P=(x,T)$ a periodic Reeb orbit, and write $z=e^{2\pi(s+it)}$. Let $u:\mathbb C\to\mathbb R^4\setminus\{0\}$ be smooth such that $a(u(z))-Ts-d$ and $\mathrm{proj}(u(z))-x(Tt)$ decay like $e^{-bs}$ in $C^\infty$ ($b>0$), where $u=e^{2a}\,\mathrm{proj}(u)$. Let $N(z):\mathbb C\to\mathbb R^4$ be real linear, smooth in $z$, and $M(t):\mathbb R^2\to\mathbb R^4$ a smooth loop of linear maps such that $e^{-2(Ts+d)}N(z)\nu-M(t)\nu$ decays like $e^{-bs}$ in $C^\infty$ for every $\nu\in\mathbb C=\mathbb R^2$. Put
--   $$\Phi(z,w)=u(z)+N(z)w,\qquad Y(\zeta,w)=e^{2T\,\mathrm{Re}\,\zeta}\bigl(x(T\,\mathrm{Im}\,\zeta)+M(\mathrm{Im}\,\zeta)w\bigr).$$
--
--   Then for every $\rho>0$ the map
--   $$(s,t,w)\mapsto e^{-2(Ts+d)}\,D\Phi(z,w)\circ\mathrm{cylScale}(s,t)-DY(it,w)$$
--   (with values in real linear maps $\mathbb C\times\mathbb C\to\mathbb R^4$) decays like $e^{-bs}$ in $C^\infty$ as $s\to+\infty$, uniformly in $t\in\mathbb R$ and $|w|<\rho$. Here $\mathrm{cylScale}(s,t)(h,k)=(2\pi z\,h,k)$ is the derivative of $(\zeta,w)\mapsto(e^{2\pi\zeta},w)$ at $(s+it,w)$.
--
--   This identifies the asymptotic first-order shape of the tube $\Phi$ around the end of $u$, after removing the radial growth, as the derivative of the model map $Y$.
--
--   Formalization Note: $\mathbb C\cong\mathbb R^2$ via `cToVec`; $a$ and $\mathrm{proj}$ are `aCoord H`, `proj H` (through `endA`, `endW` along `cylInf`); tube decay is `ExpDecayCInftyTube _ ρ b`; derivatives are `fderiv ℝ`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The rescaled derivative of the tube map converges to the derivative of its model on the tube.
Let `u : ℂ → V 1 \ {0}` be smooth with `aCoord (u) - T s - d` and `proj (u) - x(T t)` decaying like
`e^{-bs}` in `C^∞` in the coordinates `z = e^{2π(s+it)}`, let `N : ℂ → (ℂ →L[ℝ] V 1)` and a loop
`M` be smooth with `e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t)(cToVec ν)` decaying like `e^{-bs}` in `C^∞`
for every `ν`, and put `Φ(z, w) = u(z) + N(z) w`, `Y(ζ, w) = e^{2T Re ζ} (x(T Im ζ) + M(Im ζ)(cToVec w))`.
Then for every `ρ > 0`, `e^{-2(Ts+d)} DΦ(z, w) ∘ cylScale s t - DY(it, w)` decays like `e^{-bs}`
in `C^∞` on the tube, uniformly in `t` and `w ∈ ball 0 ρ`. -/
theorem expDecayCInftyTube_rescaled_fderiv_sub_model (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hM : ContDiff ℝ ∞ M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      Real.exp (-(2 * (P.T * q.1 + d))) •
          (fderiv ℝ (fun p : ℂ × ℂ => u p.1 + N p.1 p.2) (cylInf q.1 q.2.1, q.2.2)).comp
            (cylScale q.1 q.2.1) -
        fderiv ℝ (fun p : ℂ × ℂ => Real.exp (2 * P.T * p.1.re) •
          (P.x (P.T * p.1.im) + M p.1.im (cToVec p.2))) ((q.2.1 : ℂ) * Complex.I, q.2.2)) ρ b := by
  sorry

end FiniteEnergyPlane
