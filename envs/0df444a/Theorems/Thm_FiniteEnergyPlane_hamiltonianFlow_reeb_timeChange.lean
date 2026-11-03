-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hamiltonianFlow_reeb_timeChange
-- name    : FiniteEnergyPlane.hamiltonianFlow_reeb_timeChange
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T17:26:31.711277+00:00
-- url     : https://prove2.me/theorems/7b78a3b7-76be-4693-bf53-a4dca83f4943
-- title:
--   The Hamiltonian flow on a star-shaped level is a time change of the Reeb flow, also on the contact structure
-- statement:
--   Let $H:\mathbb{R}^{2n+2}\to\mathbb{R}$ have a strictly star-shaped level $S=H^{-1}(1)$, with Liouville form $\lambda_0$, Hamiltonian vector field $X_H$, Reeb field $R$ of $\lambda_0|_S$ and contact structure $\xi=\ker\lambda_0\cap TS$. Let $x:\mathbb{R}\to S$ be a trajectory of $X_H$, and let $Y$ be the linearized flow of $X_H$ along $x$ ($Y(0)=\mathrm{id}$, $Y'(t)=DX_H(x(t))\,Y(t)$). Let $Q$ be a periodic Reeb orbit with $Q(0)=x(0)$, let $\Phi$ be the linearized Reeb flow along $Q$, and put
--   $$\sigma(t)=\int_0^t\lambda_0\big(X_H(x(s))\big)\,ds .$$
--   Then for every $t\in\mathbb{R}$:
--   1. $Q(\sigma(t))=x(t)$;
--   2. for every $v\in\xi_{x(0)}$, $\pi_{x(t)}\big(Y(t)v\big)=\Phi(\sigma(t))\,v$, where $\pi_y w=w-\lambda_0(y)(w)\,R(y)$ is the projection onto $\xi_y$ along the Reeb field.
--
--   So the trajectory of $X_H$ is the Reeb orbit traversed with the time change $\sigma$, and on $\xi$ the two linearized flows agree after this time change. This lets the Conley–Zehnder index of an orbit, computed from the linearized Hamiltonian flow on $\xi$, be compared with quantities defined from the Reeb flow, such as the asymptotic operator.
--
--   **Formalization Note** The setting is `FiniteEnergyPlane` on `V n`. $X_H$ is `hamVF H`, $\lambda_0(y)(w)$ is `liouville y w`, $R$ is `reeb H`, $\pi$ is `piXi H`, and $v\in\xi_y$ is `IsInXi H y v`. The trajectory is given by `HasDerivAt x (hamVF H (x t)) t` and `x t ∈ energySurface H`; $Y$ by `Y 0 = id` and `HasDerivAt Y ((fderiv ℝ (hamVF H) (x t)).comp (Y t)) t`; $\Phi$ by `IsLinReebFlow Q Φ`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Ann. of Math. 148 (1998), Section 3; U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Sections 2.1 and 3

import Definitions.Def_FiniteEnergyPlane_Winding

open FiniteEnergyPlane

/-- On a strictly star-shaped level `S = H⁻¹(1)`, let `x` be a trajectory of `X_H` in `S`, `Y` the
linearized flow of `X_H` along `x`, `Q` a periodic Reeb orbit with `Q(0) = x(0)` and `Φ` the
linearized Reeb flow along `Q`. With `σ(t) = ∫₀ᵗ λ₀(X_H(x(s))) ds`, for all `t`: `Q(σ(t)) = x(t)`,
and for `v ∈ ξ_{x(0)}` the projection of `Y(t) v` to `ξ_{x(t)}` along the Reeb field is
`Φ(σ(t)) v`. -/
theorem FiniteEnergyPlane.hamiltonianFlow_reeb_timeChange {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (x : ℝ → V n)
    (hx : ∀ t, HasDerivAt x (hamVF H (x t)) t) (hxS : ∀ t, x t ∈ energySurface H)
    (Q : ReebOrbit H) (h0 : Q.x 0 = x 0)
    (Y : ℝ → V n →L[ℝ] V n) (hY0 : Y 0 = ContinuousLinearMap.id ℝ (V n))
    (hY : ∀ t, HasDerivAt Y ((fderiv ℝ (hamVF H) (x t)).comp (Y t)) t)
    (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow Q Φ) :
    let σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, liouville (x s) (hamVF H (x s))
    ∀ t : ℝ, Q.x (σ t) = x t ∧
      ∀ v : V n, IsInXi H (x 0) v → piXi H (x t) (Y t v) = Φ (σ t) v := by sorry
