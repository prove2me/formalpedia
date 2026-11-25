-- Prove2me | Theorems.Thm_Arxiv1110_5134_boundary_condition_frenet
-- name    : Arxiv1110_5134.boundary_condition_frenet
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:14:57.034558+00:00
-- url     : https://prove2.me/theorems/92b0301c-cd78-4473-9663-8c10c9c7101f
-- title:
--   Eqs. (33)-(34): boundary condition for the Frenet-frame Stokes vector
-- statement:
--   Let $\sigma=(\boldsymbol\Omega\times\boldsymbol\nu)\cdot\mathbf e_z\ne0$ at a boundary point $s_0$. If the Frenet-frame Stokes vector $\mathbf I(s_0,\boldsymbol\Omega)$ and the fixed-frame Stokes vector $\mathbf I_G(s_0,\boldsymbol\Omega)$ are related by Eq. (30), $\mathbf I_G=\tilde\Re(\phi_G)\mathbf I$, then (Eq. 33)
--
--   $$\mathbf I(s_0,\boldsymbol\Omega)=\tilde\Re(-\phi_G)\,\mathbf I_G(s_0,\boldsymbol\Omega).$$
--
--   If the known boundary Stokes vector is given in a left-hand frame, $\mathbf I_{G,LF}=T\mathbf I_G$, then (Eq. 34)
--
--   $$\mathbf I(s_0,\boldsymbol\Omega)=\tilde\Re(-\phi_G)\,T\,\mathbf I_{G,LF}(s_0,\boldsymbol\Omega).$$
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c012; Section 3.3, Eqs. (33)-(34), PDF pp. 15-16

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem boundary_condition_frenet (σ φ : ℝ) (hσ : σ ≠ 0) (I IG IGLF : Stokes)
    (h30 : IG = modRot σ φ *ᵥ I) :
    I = modRot σ (-φ) *ᵥ IG ∧
    (IGLF = handT *ᵥ IG → I = modRot σ (-φ) *ᵥ (handT *ᵥ IGLF)) := by sorry

end Arxiv1110_5134
