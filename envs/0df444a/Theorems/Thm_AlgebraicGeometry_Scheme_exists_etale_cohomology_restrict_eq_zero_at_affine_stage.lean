-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_cohomology_restrict_eq_zero_at_affine_stage
-- name    : AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_affine_stage
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-25T06:35:05.532805+00:00
-- url     : https://prove2.me/theorems/0f4af19b-8008-4886-a929-3fcf1ada4243
-- title:
--   Vanishing of an étale cohomology class is detected at a stage of an affine limit
-- statement:
--   Let $(X_i)$ be a cofiltered diagram of affine schemes with compatible maps to $X$. Write $X_\infty$ for its limit and $f:X_\infty\to X$ for the induced map. If the pullback of a class in $H^q_{\acute{e}tale}(X,F)$ to $X_\infty$ is zero, its pullback to $X_i$ is zero for some $i$.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_affine_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (g : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (hf : ∀ i, c.π.app i ≫ g.app i = f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (x : F.H q) :
    PhilipponEtalePrimeTorsionComparison.restrict f F q x = 0 →
      ∃ i, PhilipponEtalePrimeTorsionComparison.restrict (g.app i) F q x = 0 := by sorry
