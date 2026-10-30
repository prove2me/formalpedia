-- Prove2me | Theorems.Thm_FiniteEnergyPlane_not_isRemovablePuncture_of_tendstoCInfty_loop
-- name    : FiniteEnergyPlane.not_isRemovablePuncture_of_tendstoCInfty_loop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T20:35:31.286414+00:00
-- url     : https://prove2.me/theorems/f3ba2b16-dc10-49ff-8da4-7c0ceedd226f
-- title:
--   Loops converging to a periodic Reeb orbit exclude a removable puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ any family of linear maps, and $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ any map. Let $P=(x,T)$ be a periodic Reeb orbit on $S$, $\sigma=\pm1$, $c\in\mathbb{R}$, and $\rho_k\to0^+$. Suppose the loops $t\mapsto\mathrm{proj}\,u(\rho_ke^{-2\pi it})$ converge in $C^\infty(\mathbb{R},\mathbb{R}^{2n+2})$ to $t\mapsto x(\sigma Tt+c)$. Then the puncture $0$ of $u$ on the punctured unit disk $D\setminus\{0\}$ is not removable: $u$ does not agree on $D\setminus\{0\}$ with a smooth $\tilde J$-holomorphic map $D\to\mathbb{R}^{2n+2}\setminus\{0\}$.
--
--   This supplies the non-removability hypothesis needed to study the asymptotic behaviour of a finite-energy curve at a puncture whose boundary loops are already known to approach a periodic orbit along a sequence.
--
--   **Formalization Note** $C^\infty$ convergence of loops is `TendstoCInfty` (uniform convergence on $\mathbb{R}$ of every derivative); removability is `IsRemovablePuncture H J u 0 1`. No finite-energy or holomorphicity hypothesis on $u$ is assumed.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, with the Correction, ibid. 15 (1998), 535–538; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lemma 9.18

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u : ℂ → V n` and suppose that along some radii `ρ_k → 0⁺` the clockwise loops
`t ↦ proj(u(ρ_k e^{-2π i t}))` converge in `C^∞` to `t ↦ x(σ T t + c)` for a periodic Reeb orbit
`P = (x, T)` and `σ = ±1`. Then the puncture `0` of `u` on the punctured unit disc is not
removable. -/
theorem not_isRemovablePuncture_of_tendstoCInfty_loop {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (u : ℂ → V n)
    (P : ReebOrbit H) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k)
    (hρ0 : Tendsto ρ atTop (𝓝 0)) (c : ℝ)
    (hconv : TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ k)))
      (fun t => P.x (σ * P.T * t + c))) :
    ¬ IsRemovablePuncture H J u 0 1 := by
  sorry

end FiniteEnergyPlane
