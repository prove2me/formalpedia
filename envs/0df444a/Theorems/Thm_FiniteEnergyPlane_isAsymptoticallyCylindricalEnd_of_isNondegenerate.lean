-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isAsymptoticallyCylindricalEnd_of_isNondegenerate
-- name    : FiniteEnergyPlane.isAsymptoticallyCylindricalEnd_of_isNondegenerate
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:43:01.045124+00:00
-- url     : https://prove2.me/theorems/ade309a2-a377-4996-81bc-eddaa754574b
-- title:
--   Ends converging along a sequence to a nondegenerate orbit are asymptotically cylindrical
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $D$ the open unit disk. Let $P=(x,T)$ be a nondegenerate periodic Reeb orbit, $\sigma=\pm1$, $c\in\mathbb{R}$, and $\rho_k\to0^+$ such that the loops $t\mapsto\mathrm{proj}\,u(\rho_ke^{-2\pi it})$ converge in $C^\infty(\mathbb{R},V)$ to $t\mapsto x(\sigma Tt+c)$. Then, in the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$, $u$ is asymptotically cylindrical over $P$ with sign $\sigma$.
--
--   **Formalization Note** The conclusion is `IsAsymptoticallyCylindricalEnd H u cylEnd P σ`; the constant $c$ in it need not be the given one.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, with the Correction, ibid. 15 (1998), 535–538, Theorem 1.3; C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Definition 6.4.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer–Wysocki–Zehnder: let `u` be a finite-energy `J̃`-holomorphic curve on the punctured disk
`D \ {0}` such that, along some sequence of radii `ρₖ → 0`, the loops `t ↦ proj(u(ρₖ e^{-2πit}))`
converge in `C^∞` to `t ↦ x(σTt + c)` for a nondegenerate periodic Reeb orbit `P = (x, T)` and
`σ = ±1`. Then `u` is asymptotically cylindrical over `P` with sign `σ` at the puncture, in the
cylindrical coordinates `cylEnd`. -/
theorem isAsymptoticallyCylindricalEnd_of_isNondegenerate {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (c : ℝ) (hconv : TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ k)))
      (fun t => P.x (σ * P.T * t + c))) :
    IsAsymptoticallyCylindricalEnd H u cylEnd P σ := by
  sorry

end FiniteEnergyPlane
