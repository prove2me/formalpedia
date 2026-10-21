-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoCInfty_of_isIsolated
-- name    : FiniteEnergyPlane.tendstoCInfty_of_isIsolated
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:25:50.324068+00:00
-- url     : https://prove2.me/theorems/ce2d40fb-b725-4c13-be92-2645fe45cc1c
-- title:
--   Convergence to an isolated asymptotic orbit holds for all small radii
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$ whose puncture $0$ is not removable. Let $P=(x,T)$ be an isolated periodic Reeb orbit, $\sigma\in\{1,-1\}$, $c\in\mathbb{R}$, and $\rho_k\to0^+$ such that the loops $t\mapsto\mathrm{proj}\,u(\rho_ke^{-2\pi it})$ converge in $C^\infty$ to $t\mapsto x(\sigma Tt+c)$. Then for every $m\ge0$ and $\varepsilon>0$ there is $r_0>0$ such that for every $0<r<r_0$ some $c'\in\mathbb{R}$ satisfies
--   $$\sup_{t\in\mathbb{R}}\Big\|\frac{d^j}{dt^j}\,\mathrm{proj}\,u(re^{-2\pi it})-\frac{d^j}{dt^j}\,x(\sigma Tt+c')\Big\|\le\varepsilon\qquad(0\le j\le m).$$
--
--   **Formalization Note** Wendl phrases the conclusion with neighbourhoods in $C^\infty(S^1,M)$ of the set of parametrizations of the orbit; here the neighbourhoods are given by uniform bounds on the first $m$ derivatives. The sign $\sigma$ accounts for the single (clockwise) loop orientation used at both kinds of puncture. "Isolated" is `ReebOrbit.IsIsolated`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lemma 9.18, p. 170

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Wendl, Lemma 9.18 (p. 170). Let `u` be a finite-energy `J̃`-holomorphic curve on the punctured
unit disc whose puncture is not removable, and suppose that along some radii `ρ_k → 0⁺` the
clockwise loops `t ↦ proj(u(ρ_k e^{-2π i t}))` converge in `C^∞` to `t ↦ x(σ T t + c)`, `σ = ±1`,
for a periodic Reeb orbit `P = (x, T)`. If `P` is isolated, then for every `m` and `ε > 0`, all
loops of sufficiently small radius are within `ε` in `C^m` of some reparametrization
`t ↦ x(σ T t + c')`. -/
theorem tendstoCInfty_of_isIsolated {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (hnr : ¬ IsRemovablePuncture H J u 0 1)
    (P : ReebOrbit H) (hP : P.IsIsolated) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) (c : ℝ)
    (hconv : TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ k)))
      (fun t => P.x (σ * P.T * t + c))) :
    ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedDeriv j (loopInS H u (cwLoop 0 r)) t -
        iteratedDeriv j (fun t => P.x (σ * P.T * t + c')) t‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
