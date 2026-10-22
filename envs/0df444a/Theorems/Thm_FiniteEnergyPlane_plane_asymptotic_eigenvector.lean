-- Prove2me | Theorems.Thm_FiniteEnergyPlane_plane_asymptotic_eigenvector
-- name    : FiniteEnergyPlane.plane_asymptotic_eigenvector
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-21T12:44:04.243017+00:00
-- url     : https://prove2.me/theorems/a85c9a8d-88e7-4593-af39-eefca849bf03
-- title:
--   Asymptotic eigenvectors of finite-energy planes at nondegenerate orbits
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a nonconstant finite-energy $\tilde J$-holomorphic plane. Let $P=(x,T)$ be a nondegenerate periodic Reeb orbit, $c\in\mathbb{R}$ and $R_k\to\infty$ such that the loops $t\mapsto\mathrm{proj}\,u(R_ke^{2\pi it})$ converge in $C^\infty(\mathbb{R},V)$ to $t\mapsto x(Tt+c)$. Then, in the cylindrical coordinates $e^{2\pi(s+it)}$ at $\infty$, $u$ has exponential asymptotics over $P$ with sign $+1$ for some rate $b>0$, and $u$ has an asymptotic eigenvalue $\mu<0$ and an asymptotic eigenvector of $A_P$ there.
--
--   **Formalization Note** The conclusion is `(∃ b > 0, HasExpAsymptoticsEnd H u cylInf P 1 b) ∧ ∃ μ v, HasAsymptoticEigenvector H J u cylInf P 1 μ v`; `HasAsymptoticEigenvector` contains $\mu<0$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorems 2.10 and 2.11; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 3.13 and Corollary 6.6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Theorem 2.11 for planes: let `u` be a nonconstant finite-energy `J̃`-holomorphic
plane such that, along some sequence `Rₖ → ∞`, the loops `t ↦ proj(u(Rₖ e^{2πit}))` converge in
`C^∞` to `t ↦ x(Tt + c)` for a nondegenerate periodic Reeb orbit `P = (x, T)`. Then, in the
cylindrical coordinates `cylInf` at `∞`, `u` converges to the trivial cylinder over `P`
exponentially fast in `C^∞` and has an asymptotic eigenvalue `μ < 0` with an asymptotic
eigenvector of `A_P`. -/
theorem plane_asymptotic_eigenvector {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) (P : ReebOrbit H)
    (hP : P.IsNondegenerate) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (c : ℝ)
    (hconv : TendstoCInfty (fun k => loopInS H u (ccwLoop (R k))) (fun t => P.x (P.T * t + c))) :
    (∃ b > 0, HasExpAsymptoticsEnd H u cylInf P 1 b) ∧
      ∃ (μ : ℝ) (v : ℝ → V n), HasAsymptoticEigenvector H J u cylInf P 1 μ v := by
  sorry

end FiniteEnergyPlane
