-- Prove2me | Theorems.Thm_FiniteEnergyPlane_plane_asymptotics
-- name    : FiniteEnergyPlane.plane_asymptotics
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T23:26:03.487004+00:00
-- url     : https://prove2.me/theorems/d956e970-bdda-4dc8-943d-e7fb8ee859a0
-- title:
--   Asymptotics of finite-energy planes
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a nonconstant finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}$. Let $T=\int_{\mathbb{C}}u^*d\lambda_0$. Then $0<T<\infty$, $a(u(z))\to+\infty$ as $|z|\to\infty$, the actions of the counterclockwise loops $t\mapsto u(Re^{2\pi it})$ tend to $T$ as $R\to\infty$, and for every sequence $R_k\to\infty$ there are a subsequence $R_{k_j}$, a periodic Reeb orbit $P=(x,T)$ and $c\in\mathbb{R}$ with
--   $$\mathrm{proj}\,u\big(R_{k_j}e^{2\pi i\,\cdot}\big)\longrightarrow x(T\,\cdot+c)\quad\text{in }C^\infty(\mathbb{R},V).$$
--
--   **Formalization Note** $T$ is `(dlambdaEnergy H Set.univ u).toReal`; the first conjunct `0 < T` also rules out the value $\infty$. "$|z|\to\infty$" is the filter `cocompact ℂ`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorem 31, p. 537

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer 1993, Theorem 31 (p. 537). Let `u` be a nonconstant finite-energy `J̃`-holomorphic
plane, and `T > 0` its `dλ`-energy. Then `a(u(z)) → +∞` as `z → ∞`, the actions of the
counterclockwise loops `t ↦ u(R e^{2π i t})` tend to `T`, and for every `R_k → ∞` a subsequence of
the loops `t ↦ proj(u(R_k e^{2π i t}))` converges in `C^∞` to `t ↦ x(T t + c)` for a periodic Reeb
orbit `(x, T)`. -/
theorem plane_asymptotics {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    0 < (dlambdaEnergy H Set.univ u).toReal ∧
      Tendsto (fun z => aCoord H (u z)) (cocompact ℂ) atTop ∧
      Tendsto (fun R => loopAction H u (ccwLoop R)) atTop
        (𝓝 (dlambdaEnergy H Set.univ u).toReal) ∧
      ∀ R : ℕ → ℝ, Tendsto R atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H,
        P.T = (dlambdaEnergy H Set.univ u).toReal ∧ ∃ c : ℝ,
          TendstoCInfty (fun k => loopInS H u (ccwLoop (R (φ k)))) (fun t => P.x (P.T * t + c)) := by
  sorry

end FiniteEnergyPlane
