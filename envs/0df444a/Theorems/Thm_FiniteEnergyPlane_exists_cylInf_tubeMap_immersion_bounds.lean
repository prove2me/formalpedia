-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_cylInf_tubeMap_immersion_bounds
-- name    : FiniteEnergyPlane.exists_cylInf_tubeMap_immersion_bounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T18:07:13.097807+00:00
-- url     : https://prove2.me/theorems/1ab0f468-794c-498d-9ad4-ba887931f85e
-- title:
--   Uniform immersion bounds of a tube map on a cylindrical end
-- statement:
--   Setting of `exists_cylBounds_tubeMap`: $H$ is a strictly star-shaped level, $P$ a Reeb orbit of period $T$, $u:\mathbb{C}\to V$ smooth and nonvanishing with exponential $C^\infty$ asymptotics at $P$ (`ha`, `hw`, rate $b>0$, shift $d$), $N:\mathbb{C}\to \mathcal{L}(\mathbb{C},V)$ smooth with $Du(z)\Delta + N(z)\nu = 0 \Rightarrow \Delta=\nu=0$, $M$ a unitary $\xi$-frame along $P$, and $e^{-2(Ts+d)}N(e^{2\pi(s+it)})\nu \to M(t)\nu$ exponentially in $C^\infty$ (`hNM`).
--
--   For $(s,t,w)\in\mathbb{R}\times\mathbb{R}\times\mathbb{C}$ put $\zeta = e^{2\pi(s+it)}$ and
--   $$\Xi(s,t,w) = \big(\mathrm{aCoord}(u(\zeta)+N(\zeta)w),\ \mathrm{proj}(u(\zeta)+N(\zeta)w)\big).$$
--   Then there are $r>0$, $c>0$ and $s_0$ such that on the region $(s_0,\infty)\times\mathbb{R}\times B(0,r)$:
--   - $u(\zeta)+N(\zeta)w \ne 0$;
--   - $\Xi$ is smooth;
--   - for every $m\ge 1$ there are $C, s_1$ with $\|D^m\Xi(q)\|\le C$ for all $q$ in the region with $q_1 \ge s_1$;
--   - $c\|h\| \le \|D\Xi(q)h\|$ for all $q$ in the region and all $h$.
--
--   Role: uniform immersion bounds of the tube map in cylindrical coordinates on the positive end; used to transfer uniform derivative bounds from images to tube coordinates.
--
--   Formalization note: derivatives are `iteratedFDeriv ℝ m` and `fderiv ℝ`; the region is `Set.Ioi s₀ ×ˢ Set.univ ×ˢ Metric.ball 0 r`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Uniform immersion bounds for a tube map in cylindrical coordinates. In the setting of
`exists_cylBounds_tubeMap`, let `Ξ(s, t, w) = (aCoord, proj)(u ζ + N ζ w)` with `ζ = e^{2π(s+it)}`.
Then for some `r, c > 0` and `s₀`, on `(s₀, ∞) × ℝ × ball 0 r` the map `u ζ + N ζ w` is nonzero,
`Ξ` is smooth, every derivative `D^m Ξ` with `m ≥ 1` is bounded for large `s`, and
`c ‖h‖ ≤ ‖DΞ h‖`. -/
theorem exists_cylInf_tubeMap_immersion_bounds (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ r > 0, ∃ c > 0, ∃ s₀ : ℝ,
      (∀ q ∈ Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) r,
        u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2 ≠ 0) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ =>
          (aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2),
            proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2)))
        (Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) r) ∧
      (∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ q ∈ Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) r, s₁ ≤ q.1 →
        ‖iteratedFDeriv ℝ m (fun q : ℝ × ℝ × ℂ =>
          (aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2),
            proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2))) q‖ ≤ C) ∧
      ∀ q ∈ Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) r, ∀ h : ℝ × ℝ × ℂ,
        c * ‖h‖ ≤ ‖fderiv ℝ (fun q : ℝ × ℝ × ℂ =>
          (aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2),
            proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2))) q h‖ := by
  sorry

end FiniteEnergyPlane
