-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasDerivAt_unitaryFrame_apply_of_linearized
-- name    : FiniteEnergyPlane.hasDerivAt_unitaryFrame_apply_of_linearized
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:49:51.261253+00:00
-- url     : https://prove2.me/theorems/c80768a1-8e23-4c5e-9045-175c793a7b06
-- title:
--   Solutions of the linearized equation in a unitary frame solve the linearized Reeb flow
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, with a $d\lambda_0$-compatible complex structure $J$ on $\xi$. Let $P = (x, T)$ be a periodic Reeb orbit, $Z$ a unitary frame of $\xi$ along $P$, and $S_\infty$ a loop of symmetric matrices representing the asymptotic operator in this frame: $A_P(Z\eta) = Z(-J_0\eta' - S_\infty\eta)$ for smooth $1$-periodic $\eta$.
--
--   If $\zeta : \mathbb{R} \to \mathbb{R}^2$ solves $\zeta' = J_0 S_\infty(t)\,\zeta$, then $h(\tau) = Z(\tau/T)\,\zeta(\tau/T)$ solves the linearized Reeb equation along $P$:
--   $$h'(\tau) = DR(x(\tau))\,h(\tau) \qquad \text{for all } \tau \in \mathbb{R}.$$
--
--   Role: identifies solutions of the frame equation with solutions of the linearized Reeb flow, including non-periodic ones.
--
--   Formalization Note: `hA` is the frame representation of the asymptotic operator supplied by `FiniteEnergyPlane.asympOp_frame_bridge`; $R$ is `reeb H` and $DR$ is `fderiv ℝ (reeb H)`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2; H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Section 5

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Solutions of the linearized equation in a unitary frame. Let `Z` be a unitary frame of `ξ`
along the periodic Reeb orbit `P = (x, T)`, and let `S∞` be the loop of symmetric matrices that
represents the asymptotic operator in this frame. If `ζ` solves `ζ' = J₀ S∞(t) ζ`, then
`h(τ) = Z(τ/T) ζ(τ/T)` solves the linearized Reeb equation `h'(τ) = DR(x(τ)) h(τ)`. -/
theorem hasDerivAt_unitaryFrame_apply_of_linearized (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (ζ : ℝ → CauchyRiemannIndex.Vec 1)
    (hζ : ∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t)
    (τ : ℝ) :
    HasDerivAt (fun τ => Z (τ / P.T) (ζ (τ / P.T)))
      (fderiv ℝ (reeb H) (P.x τ) (Z (τ / P.T) (ζ (τ / P.T)))) τ := by
  sorry

end FiniteEnergyPlane
