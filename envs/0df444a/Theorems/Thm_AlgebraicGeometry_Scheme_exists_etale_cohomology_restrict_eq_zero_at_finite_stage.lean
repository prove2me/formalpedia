-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_cohomology_restrict_eq_zero_at_finite_stage
-- name    : AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_finite_stage
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-25T01:14:41.248818+00:00
-- url     : https://prove2.me/theorems/0ba99e69-35fe-47a9-875f-2ddf2fae8e69
-- title:
--   Vanishing of an étale cohomology class descends to a stage of an affine inverse limit
-- statement:
--   Take a cofiltered limit $V=\varprojlim_i V_i$ of finite schemes over
--       an affine scheme $Y$, and a closed subscheme $W\hookrightarrow Y$. For an abelian étale sheaf
--       $F$ on $W$, a class in $H^q(W,F)$ that restricts to zero on $W\times_Y V$ already restricts
--       to zero on $W\times_Y V_i$ for some $i$.
-- source:
--   Vanishing consequence of Stacks Project, Lemma 59.51.5, https://stacks.math.columbia.edu/tag/03Q6.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_finite_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c)
    {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
    (t : D ⟶ (Functor.const I).obj Y) (f : c.pt ⟶ Y)
    (_ : ∀ i, c.π.app i ≫ t.app i = f) (_ : ∀ i, IsFinite (t.app i))
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (x : F.H q) :
    PhilipponEtalePrimeTorsionComparison.restrict (pullback.fst j f) F q x = 0 →
      ∃ i, PhilipponEtalePrimeTorsionComparison.restrict (pullback.fst j (t.app i)) F q x = 0 := by sorry
