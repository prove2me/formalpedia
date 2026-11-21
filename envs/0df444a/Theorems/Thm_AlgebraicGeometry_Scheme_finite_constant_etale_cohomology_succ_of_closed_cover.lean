-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_succ_of_closed_cover
-- name    : AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_succ_of_closed_cover
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-20T18:09:36.643368+00:00
-- url     : https://prove2.me/theorems/2b9772e9-1561-49ae-af9e-9840879d5b05
-- title:
--   Finiteness of étale cohomology on a cover by two closed subschemes
-- statement:
--   Let $i\colon Y\to X$ and $j\colon Z\to X$ be closed immersions whose images cover $X$.
--   Let $T=Y\times_X Z$, let $A$ be an abelian group, and denote the constant coefficient sheaf on
--   each small étale site by $\underline A$. For $q\geq 0$, if
--   $$H^{q+1}_{\mathrm{et}}(Y,\underline A),\qquad
--   H^{q+1}_{\mathrm{et}}(Z,\underline A),\qquad H^q_{\mathrm{et}}(T,\underline A)$$
--   are finite, then $H^{q+1}_{\mathrm{et}}(X,\underline A)$ is finite. This gives a finiteness
--   criterion that uses the scheme-theoretic intersection of the closed pieces.
-- source:
--   Consequence of the closed-immersion direct image comparison (Stacks Project, Section 59.46, https://stacks.math.columbia.edu/tag/04E1) and the long exact cohomology sequence (Section 59.50, https://stacks.math.columbia.edu/tag/03Q3).

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_succ_of_closed_cover
    {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i ∪ Set.range j = Set.univ)
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (hy : Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H (q + 1)))
    (hz : Finite (((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H (q + 1)))
    (ht : Finite (((constantSheaf (pullback i j).smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H (q + 1)) := by sorry
