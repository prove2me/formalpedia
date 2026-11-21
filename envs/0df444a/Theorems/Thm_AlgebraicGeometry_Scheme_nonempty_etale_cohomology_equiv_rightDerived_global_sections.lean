-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_equiv_rightDerived_global_sections
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_rightDerived_global_sections
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T21:02:46.434051+00:00
-- url     : https://prove2.me/theorems/c7107d5b-aa4e-48f1-ba51-4295d4c20c18
-- title:
--   Étale Ext cohomology agrees with derived global sections
-- statement:
--   Let $X$ be a scheme and let $F$ be an abelian sheaf on its small étale site. Write $\Gamma_X$ for evaluation at the terminal object of that site and $\underline{\mathbf Z}$ for the constant integer sheaf. For each $n\geq0$ there is an additive isomorphism
--   $$\operatorname{Ext}^n(\underline{\mathbf Z},F)\simeq (R^n\Gamma_X)(F).$$
--   This identifies the Ext definition of étale sheaf cohomology with the definition by derived global sections used in proper base change.
-- source:
--   Stacks Project, Cohomology on Sites, Section 21.2, https://stacks.math.columbia.edu/tag/01FT.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
import Mathlib.CategoryTheory.Abelian.RightDerived

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Opposite
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_rightDerived_global_sections
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    let Γ := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (Scheme.Etale.mk (𝟙 X)))
    letI : Γ.Additive := ⟨by intros; rfl⟩
    Nonempty (F.H n ≃+ ((Γ.rightDerived n).obj F)) := by sorry
