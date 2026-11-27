-- Prove2me | Theorems.Thm_Arxiv1810_02867_scalar_wave_equation
-- name    : Arxiv1810_02867.scalar_wave_equation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T05:21:00.854665+00:00
-- url     : https://prove2.me/theorems/37f5cc12-2233-47b8-bad5-d576a8108669
-- title:
--   Eq. (3): unified scalar wave equation for non-reciprocal media
-- statement:
--   Let $\alpha(\mathbf x)$, $\beta_{rs}(\mathbf x)$, $\gamma_r(\mathbf x)$ be time-independent parameters on the plane. Let $\beta$ be symmetric and invertible at every point, with inverse $\vartheta_{rs}$ ($\vartheta_{rs}\beta_{su}=\delta_{ru}$), and let $\beta,\gamma$ be $C^1$. Let $P$ and $Q_r$ be $C^2$ functions of $(\mathbf x,t)$ which, with sources $B,C_r$, satisfy the unified equations (1)-(2) at every point and time:
--   $$\alpha\partial_tP+(\partial_r+\gamma_r\partial_t)Q_r=B,\qquad (\partial_r+\gamma_r\partial_t)P+\beta_{rs}\partial_tQ_s=C_r.$$
--   Then $P$ satisfies the scalar wave equation (3):
--   $$(\partial_r+\gamma_r\partial_t)\vartheta_{rs}(\partial_s+\gamma_s\partial_t)P-\alpha\partial_t^2P=(\partial_r+\gamma_r\partial_t)\vartheta_{rs}C_s-\partial_tB,$$
--   where each operator acts on everything to its right.
--
--   **Formalization Note** The paper leaves the smoothness unstated. The $C^2$ assumption on the fields and the $C^1$ assumption on $\beta,\gamma$ are the standing convention that the derivation needs (it commutes $\partial_t$ with $\partial_r$).
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c001; Section II, eq. (3), PDF p. 4; derivation Appendix A.4, eqs. (A71)-(A78), PDF pp. 28-29

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem scalar_wave_equation (alpha : Plane → ℝ) (beta : Plane → Fin 2 → Fin 2 → ℝ)
    (gamma : Plane → Fin 2 → ℝ) (P : Plane → ℝ → ℝ) (Q : Plane → ℝ → Fin 2 → ℝ)
    (B : Plane → ℝ → ℝ) (C : Plane → ℝ → Fin 2 → ℝ)
    (hsym : ∀ x r s, beta x r s = beta x s r) (hdet : ∀ x, (Matrix.of (beta x)).det ≠ 0)
    (hP : ContDiff ℝ 2 (fun z : Plane × ℝ => P z.1 z.2))
    (hQ : ContDiff ℝ 2 (fun z : Plane × ℝ => Q z.1 z.2))
    (hbeta : ContDiff ℝ 1 beta) (hgamma : ContDiff ℝ 1 gamma)
    (h : UnifiedEqs alpha beta gamma P Q B C) :
    ∀ x t, ∑ r, Dg gamma r (fun y s => ∑ u, thetaOf (beta y) r u * Dg gamma u P y s) x t -
        alpha x * pdt (pdt P) x t =
      ∑ r, Dg gamma r (fun y s => ∑ u, thetaOf (beta y) r u * C y s u) x t - pdt B x t := by sorry

end Arxiv1810_02867
