-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_prop_2_bij
-- name    : FixedRankGeom.PSD.prop_2_bij
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:40.729441+00:00
-- url     : https://prove2.me/theorems/fed13bd8-9715-469d-89d2-54ae4acc4a46
-- title:
--   Proposition 2, p. 18 — L^{r+}_Y(θ) = Yθᵀ + θYᵀ is a linear bijection H_Y M̄^{q1}_{r+} → T_X M^e_{r+}
-- statement:
--   Let $0<r\le p$, $Y\in\mathbb R_*^{p\times r}$, $X=YY^\top$, and let $W_Y$ be symmetric positive definite. The linear map
--   $$\mathcal L^{r+}_Y(\theta_Y)=Y\theta_Y^\top+\theta_YY^\top$$
--   restricts to a bijection from the horizontal space $\mathcal H_Y\bar{\mathcal M}^{q_1}_{r+}$ (the $\bar g_Y$-orthogonal complement of $\{Y\Omega:\Omega=-\Omega^\top\}$) onto the tangent space $T_X\mathcal M^e_{r+}$.
--
--   This bijection transports the quotient Hessian onto the embedded Hessian in Theorem 3.
--
--   **Formalization Note** The paper builds $\mathcal L^{r+}_Y$ by the block formula (22) in the basis $[U\ U_\perp]$ and then shows it equals $Y\theta_Y^\top+\theta_YY^\top$; here the map is defined by the latter expression, which is linear, and the content is the bijectivity.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 18, Proposition 2, (22)

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Proposition 2, p. 18: `L^{r+}_Y(θ) = Yθᵀ + θYᵀ` is a bijection `H_Y M̄^{q1}_{r+} → T_X M^e_{r+}`,
`X = YYᵀ`. -/
theorem prop_2_bij {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (W : Mat p r → Mat r r) (Y : Mat p r) (hY : Y ∈ fullRankSet p r)
    (hW : (toMat (W Y)).PosDef) :
    Set.BijOn (Lmap Y) (horizontalSpace W Y) (tangentSpace (psdRankSet p r) (gram Y)) := by sorry

end FixedRankGeom.PSD
