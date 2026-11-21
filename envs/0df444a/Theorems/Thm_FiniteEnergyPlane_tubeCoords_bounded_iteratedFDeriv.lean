-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tubeCoords_bounded_iteratedFDeriv
-- name    : FiniteEnergyPlane.tubeCoords_bounded_iteratedFDeriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T18:07:13.456899+00:00
-- url     : https://prove2.me/theorems/cd1cf705-5ca7-45fc-aabb-705e6e1e2208
-- title:
--   Uniform derivative bounds of tube coordinates on a cylindrical end
-- statement:
--   Setting of `exists_cylBounds_tubeMap`: $H$ is a strictly star-shaped level, $P$ a Reeb orbit of period $T$, $u:\mathbb{C}\to V$ smooth and nonvanishing with exponential $C^\infty$ asymptotics at $P$ (`ha`, `hw`, rate $b>0$, shift $d$), $N:\mathbb{C}\to\mathcal{L}(\mathbb{C},V)$ smooth with $Du(z)\Delta + N(z)\nu = 0 \Rightarrow \Delta=\nu=0$, $M$ a unitary $\xi$-frame along $P$, and $e^{-2(Ts+d)}N(e^{2\pi(s+it)})\nu\to M(t)\nu$ exponentially in $C^\infty$ (`hNM`).
--
--   Let $\psi, v:\mathbb{C}\to\mathbb{C}$ be smooth with $\|D\psi - \mathrm{id}\|\le 1/2$ everywhere and $v(z)\to 0$ as $z\to\infty$, and let $f = u\circ\psi + (N\circ\psi)\,v$ have exponential $C^\infty$ asymptotics at $P$: $\mathrm{endA}(f) - Ts - d_f$ and $\mathrm{endW}(f) - x(Tt + c_f)$ decay like $e^{-b_f s}$ in $C^\infty$, $b_f>0$.
--
--   Then for every $m\ge 0$ there are $C, s_1$ such that for all $s\ge s_1$ and all $t$,
--   $$\big\|D^m_{(s,t)}\big[\psi(z)/z\big]\big\| \le C,\qquad \big\|D^m_{(s,t)}\big[v(z)\big]\big\|\le C,\qquad z = e^{2\pi(s+it)}.$$
--
--   Role: uniform $C^\infty$ bounds of the tube coordinates of a map close to a reference end, in cylindrical coordinates.
--
--   Formalization note: `cylInf s t = exp(2πs)·exp(2πit)`; derivatives are `iteratedFDeriv ℝ m` of functions of `p : ℝ × ℝ`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Bounded derivatives of tube coordinates on the end. In the setting of
`exists_cylBounds_tubeMap`, let `f = u ∘ ψ + (N ∘ ψ) v` with `ψ`, `v` smooth,
`‖Dψ - id‖ ≤ 1/2` and `v → 0` at `∞`, and let `f` have exponential `C^∞` asymptotics at `P`
(`hfa`, `hfw`). Then in the coordinates `z = e^{2π(s+it)}`, every derivative of `ψ(z)/z` and of
`v(z)` is bounded for large `s`, uniformly in `t`. -/
theorem tubeCoords_bounded_iteratedFDeriv (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (ψ v : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hv0 : Tendsto v (cocompact ℂ) (𝓝 0)) :
    ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2) (s, t)‖ ≤ C ∧
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (s, t)‖ ≤ C := by
  sorry

end FiniteEnergyPlane
