-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ReebOrbit_apply_eq_apply_add_of_apply_eq
-- name    : FiniteEnergyPlane.ReebOrbit.apply_eq_apply_add_of_apply_eq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-25T23:13:05.505873+00:00
-- url     : https://prove2.me/theorems/32abec71-a399-4dd7-bcc4-d7a39a461707
-- title:
--   Reeb trajectories through a common point differ by a time shift
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with Reeb field $R=X_H/\lambda_0(X_H)$, and let $P=(x,T)$ and $Q=(y,T')$ be periodic Reeb orbits on $S$ (so $x'=R(x)$, $y'=R(y)$, with images in $S$). If $y(\tau_1)=x(\tau_2)$ for some $\tau_1,\tau_2\in\mathbb R$, then
--   $$y(\tau)=x(\tau+\tau_2-\tau_1)\qquad\text{for all }\tau\in\mathbb R .$$
--   Both sides solve the ODE $z'=R(z)$ on $S$ with the same value at $\tau=\tau_1$; since $\lambda_0(X_H)>0$ on $S$, the field $R$ is smooth, hence locally Lipschitz, on a neighbourhood of $S$, and uniqueness of solutions of ODEs gives the claim.
-- source:
--   H. Hofer, Invent. Math. 114 (1993), § 1 (Reeb flow); uniqueness of ODE solutions. Used in C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, proof of Lemma 9.18, p. 170

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Uniqueness of Reeb trajectories on a strictly star-shaped level: if two periodic Reeb orbits
`P = (x, T)` and `Q = (y, T')` meet, `y(τ₁) = x(τ₂)`, then `y(τ) = x(τ + τ₂ - τ₁)` for all `τ`. -/
theorem ReebOrbit.apply_eq_apply_add_of_apply_eq {n : ℕ} {H : V n → ℝ}
    (hH : IsStrictlyStarShapedLevel H) (P Q : ReebOrbit H) {τ₁ τ₂ : ℝ} (h : Q.x τ₁ = P.x τ₂) :
    ∀ τ, Q.x τ = P.x (τ + (τ₂ - τ₁)) := by
  sorry

end FiniteEnergyPlane
