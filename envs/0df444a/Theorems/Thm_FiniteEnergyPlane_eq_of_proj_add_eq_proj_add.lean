-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_of_proj_add_eq_proj_add
-- name    : FiniteEnergyPlane.eq_of_proj_add_eq_proj_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T20:51:37.478772+00:00
-- url     : https://prove2.me/theorems/f1d38513-98a1-4e7d-a681-1cf1651a33df
-- title:
--   Local injectivity of the tube map around a periodic Reeb orbit
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $P=(x,T)$ a periodic Reeb orbit on $S$. There are $\varepsilon,\rho>0$ such that for all $\tau,\tau'\in\mathbb{R}$ and $h\in\xi_{x(\tau)}$, $h'\in\xi_{x(\tau')}$ with $|\tau-\tau'|\le\varepsilon$ and $\|h\|,\|h'\|\le\rho$,
--   $$\mathrm{proj}(x(\tau)+h)=\mathrm{proj}(x(\tau')+h')\ \Longrightarrow\ \tau=\tau'\ \text{and}\ h=h'.$$
--   Here $\mathrm{proj}$ is the radial projection onto $S$ and $\xi_y=\ker\lambda_0(y)\cap\ker dH(y)$ (`IsInXi`).
--
--   Role: uniform local injectivity of the tube map $(\tau,h)\mapsto\mathrm{proj}(x(\tau)+h)$ in which asymptotic formulas such as Hryniewicz's Theorem 2.11 are written.
--
--   **Formalization Note** $P$ need not be prime or nondegenerate; the conclusion is only local in $\tau$. Norms are the sup norm on $\mathbb{R}^{2n+2}$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22 / (100); U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.11

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- The tube map `(τ, h) ↦ proj (x(τ) + h)`, `h ∈ ξ_{x(τ)}`, around a periodic Reeb orbit
`P = (x, T)` on a strictly star-shaped level is locally injective, uniformly along `P`: there are
`ε, ρ > 0` such that `proj (x(τ) + h) = proj (x(τ') + h')` with `|τ - τ'| ≤ ε`, `h ∈ ξ_{x(τ)}`,
`h' ∈ ξ_{x(τ')}` and `‖h‖, ‖h'‖ ≤ ρ` forces `τ = τ'` and `h = h'`. -/
theorem eq_of_proj_add_eq_proj_add {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) :
    ∃ ε > 0, ∃ ρ > 0, ∀ (τ τ' : ℝ) (h h' : V n), |τ - τ'| ≤ ε →
      IsInXi H (P.x τ) h → IsInXi H (P.x τ') h' → ‖h‖ ≤ ρ → ‖h'‖ ≤ ρ →
      proj H (P.x τ + h) = proj H (P.x τ' + h') → τ = τ' ∧ h = h' := by
  sorry

end FiniteEnergyPlane
