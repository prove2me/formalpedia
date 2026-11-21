-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eq_add_int_mul_of_proj_add_eq_of_isPrime
-- name    : FiniteEnergyPlane.exists_eq_add_int_mul_of_proj_add_eq_of_isPrime
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T23:45:41.411208+00:00
-- url     : https://prove2.me/theorems/4273f984-9a57-4ab8-8de0-adb490d7de4c
-- title:
--   Injectivity of the tube map around a prime orbit modulo the period
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $P=(x,T)$ a prime periodic Reeb orbit on $S$ ($x(\tau)\neq x(0)$ for $0<\tau<T$). There is $\rho>0$ such that for all $\tau_1,\tau_2\in\mathbb{R}$ and $h_i\in\xi_{x(\tau_i)}$ with $\|h_1\|,\|h_2\|\le\rho$,
--   $$\mathrm{proj}(x(\tau_1)+h_1)=\mathrm{proj}(x(\tau_2)+h_2)\ \Longrightarrow\ \tau_1=\tau_2+jT\ \text{for some } j\in\mathbb{Z}\ \text{and}\ h_1=h_2 .$$
--   Here $\mathrm{proj}$ is the radial projection onto $S$ and $\xi_y=\ker\lambda_0(y)\cap\ker dH(y)$ (`IsInXi`).
--
--   Role: global (modulo the period) injectivity of the tube map $(\tau,h)\mapsto\mathrm{proj}(x(\tau)+h)$ in which the asymptotic formulas of planes over $P$ are written; used to compare two such formulas at a common point.
--
--   **Formalization Note** No restriction on $|\tau_1-\tau_2|$ is imposed. Norms are the sup norm.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.23; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, proof of Theorem 4.11

import Definitions.Def_FiniteEnergyPlane_Setting
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- The tube map `(τ, h) ↦ proj (x(τ) + h)`, `h ∈ ξ_{x(τ)}`, around a prime periodic Reeb orbit
`P = (x, T)` on a strictly star-shaped level is injective modulo the period for small `h`: there
is `ρ > 0` such that `proj (x(τ₁) + h₁) = proj (x(τ₂) + h₂)` with `h_i ∈ ξ_{x(τ_i)}` and
`‖h₁‖, ‖h₂‖ ≤ ρ` forces `τ₁ = τ₂ + jT` for some integer `j` and `h₁ = h₂`. -/
theorem exists_eq_add_int_mul_of_proj_add_eq_of_isPrime {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsPrime) :
    ∃ ρ > 0, ∀ (τ₁ τ₂ : ℝ) (h₁ h₂ : V n), IsInXi H (P.x τ₁) h₁ → IsInXi H (P.x τ₂) h₂ →
      ‖h₁‖ ≤ ρ → ‖h₂‖ ≤ ρ → proj H (P.x τ₁ + h₁) = proj H (P.x τ₂ + h₂) →
      ∃ j : ℤ, τ₁ = τ₂ + j * P.T ∧ h₁ = h₂ := by
  sorry

end FiniteEnergyPlane
