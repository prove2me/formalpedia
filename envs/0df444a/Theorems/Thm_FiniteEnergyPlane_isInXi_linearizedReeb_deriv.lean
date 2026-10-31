-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isInXi_linearizedReeb_deriv
-- name    : FiniteEnergyPlane.isInXi_linearizedReeb_deriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T11:03:26.393574+00:00
-- url     : https://prove2.me/theorems/03ab873e-df3e-420b-963e-b937fb328206
-- title:
--   The asymptotic-operator expression of a contact-plane section stays in the contact plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level with contact planes $\xi$, $P=(x,T)$ a periodic Reeb orbit, and $\eta:\mathbb{R}\to\mathbb{R}^{2n+2}$ differentiable with $\eta(t)\in\xi_{x(Tt)}$ for all $t$. Then for all $t$, $$-\eta'(t)+T\,DR(x(Tt))\,\eta(t)\in\xi_{x(Tt)}.$$
--
--   This is the expression to which $J$ is applied in the asymptotic operator $A_P\eta=J(-\eta'+T\,DR\,\eta)$, so the statement says that $A_P$ is well defined on sections of $\xi$ along $P$.
--
--   **Formalization Note** `V n` is $\mathbb{R}^{2n+2}$, `IsStrictlyStarShapedLevel H` says $H$ is smooth and $S=H^{-1}(1)$ is strictly star-shaped with $dH(x)x>0$ on $S$, `reeb H` is the Reeb field $R=X_H/\lambda_0(X_H)$, `liouville x v` is $\lambda_0(x)v=\tfrac12\omega_0(x,v)$, `IsInXi H x v` means $v\in\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$, and a `ReebOrbit H` is $P=(x,T)$ with $x'=R(x)$, $x(\mathbb{R})\subset S$, $x(\tau+T)=x(\tau)$, $T>0$.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

/-- Let `P = (x, T)` be a periodic Reeb orbit and `η` a differentiable family with
`η(t) ∈ ξ_{x(Tt)}` for all `t`. Then `-η'(t) + T DR(x(Tt)) η(t) ∈ ξ_{x(Tt)}` for all `t`. -/
theorem isInXi_linearizedReeb_deriv {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (η : ℝ → V n) (hη : Differentiable ℝ η)
    (hξ : ∀ t : ℝ, IsInXi H (P.x (P.T * t)) (η t)) (t : ℝ) :
    IsInXi H (P.x (P.T * t)) (-(deriv η t) + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t)) := by
  sorry

end FiniteEnergyPlane
