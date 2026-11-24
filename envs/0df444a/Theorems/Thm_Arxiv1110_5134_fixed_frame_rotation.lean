-- Prove2me | Theorems.Thm_Arxiv1110_5134_fixed_frame_rotation
-- name    : Arxiv1110_5134.fixed_frame_rotation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:13:33.852152+00:00
-- url     : https://prove2.me/theorems/7efd4c4a-321b-4240-9561-7037f213d93c
-- title:
--   Eqs. (26)-(32): Frenet-frame and fixed-frame Stokes vectors (as corrected)
-- statement:
--   Let $\sigma=(\boldsymbol\Omega\times\boldsymbol\nu)\cdot\mathbf e_z$ and let $\phi_G$ be the rotation angle between the Frenet-Serret frame and the fixed-reference frame. Then:
--
--   - $\Re(-\phi_G)\Re(\phi_G)=1$, so Eq. (27) inverts Eq. (26);
--   - the modified rotation matrix $\tilde\Re(\phi_G)=\tfrac12(1+\operatorname{sgn}\sigma)\Re(\phi_G)+\tfrac12(1-\operatorname{sgn}\sigma)\Re(-\phi_G)$ equals $\Re(\phi_G)$ if $\sigma>0$ (Eq. 26) and $\Re(-\phi_G)$ if $\sigma<0$ (Eq. 29), so Eq. (30), $\mathbf I_G=\tilde\Re(\phi_G)\mathbf I$, unifies both cases;
--   - if $\sigma\ne0$, then $\tilde\Re(-\phi_G)$ is the inverse of $\tilde\Re(\phi_G)$, and $\mathbf I_G=\tilde\Re(\phi_G)\mathbf I$ if and only if $\mathbf I=\tilde\Re(-\phi_G)\mathbf I_G$ (Eq. 32).
--
--   **Formalization Note** As printed, Eq. (31) has the factor $\tfrac12$ before the first term only, which would give $2\Re(-\phi_G)$ when $\sigma<0$, contradicting Eq. (29). The statement uses $\tfrac12$ on both terms, which is what Eqs. (26), (29) and (30) require. The formula (28) for $\cos\phi_G$ is not stated (see the report).
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c011; Section 3.3, Eqs. (26), (27), (29)-(32), PDF pp. 14-15

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem fixed_frame_rotation (σ φ : ℝ) :
    stokesRot (-φ) * stokesRot φ = 1 ∧
    (0 < σ → modRot σ φ = stokesRot φ) ∧
    (σ < 0 → modRot σ φ = stokesRot (-φ)) ∧
    (σ ≠ 0 → modRot σ (-φ) * modRot σ φ = 1 ∧ modRot σ φ * modRot σ (-φ) = 1) ∧
    (σ ≠ 0 → ∀ I IG : Stokes, IG = modRot σ φ *ᵥ I ↔ I = modRot σ (-φ) *ᵥ IG) := by sorry

end Arxiv1110_5134
