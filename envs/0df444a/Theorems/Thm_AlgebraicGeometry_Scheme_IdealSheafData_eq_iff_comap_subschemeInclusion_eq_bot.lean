-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.eq_iff_comap_subschemeInclusion_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/5700c699-fd92-5c9e-b87f-6013aa1f57fd
-- title:
--   Equality of ideal sheaves via vanishing comaps
-- statement:
--   Let $W$ be a scheme (in a fixed universe) and let $I_1, I_2$ be two elements of `W.IdealSheafData`, i.e. two quasi-coherent ideal sheaves on $W$ recorded by their local ideal data. Each $I_j$ determines a closed subscheme together with its canonical closed immersion $I_j$`.subschemeι` into $W$, and for an ideal sheaf $J$ on $W$ one may form its comap (inverse image ideal sheaf) along a morphism. The assertion is the equivalence: $I_1 = I_2$ holds if and only if both of the following hold — the comap of $I_2$ along the closed immersion of the subscheme cut out by $I_1$ is the bottom ideal sheaf (the zero ideal, i.e. $I_2$ pulls back to $0$ on the closed subscheme defined by $I_1$), and symmetrically the comap of $I_1$ along the closed immersion of the subscheme cut out by $I_2$ is the bottom ideal sheaf. No further hypotheses are imposed on $W$, $I_1$ or $I_2$.
--
--   This is the scheme-theoretic criterion that an ideal sheaf is determined by the closed subscheme it cuts out, phrased as mutual vanishing of each ideal on the other's closed subscheme. It is used in the representability analysis of relative Drinfeld basis loci, where it supplies the uniqueness half of the characterisation [`WeierstrassProjModel.RelativeGroupLaw.exists_idealSheafData_comap_eq_bot_iff_isDrinfeldBasisOver`](thm.html#WeierstrassProjModel.RelativeGroupLaw.exists_idealSheafData_comap_eq_bot_iff_isDrinfeldBasisOver).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_iff_comap_subschemeInclusion_eq_bot
    {W : Scheme.{u}} (I₁ I₂ : W.IdealSheafData) :
    I₁ = I₂ ↔ I₂.comap I₁.subschemeι = ⊥ ∧ I₁.comap I₂.subschemeι = ⊥ := by sorry
