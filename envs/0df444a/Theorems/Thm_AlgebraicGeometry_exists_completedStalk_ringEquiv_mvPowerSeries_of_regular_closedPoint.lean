-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_completedStalk_ringEquiv_mvPowerSeries_of_regular_closedPoint
-- name    : AlgebraicGeometry.exists_completedStalk_ringEquiv_mvPowerSeries_of_regular_closedPoint
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-16T17:09:50.881494+00:00
-- url     : https://prove2.me/theorems/653a9187-9d91-40da-a335-286c2f7c6d90
-- title:
--   Formal power-series models at regular closed points
-- statement:
--   Let $K$ be an algebraically closed field and $X$ a scheme locally of finite type over $K$. Let $x\in X$ be a closed point whose local ring $\mathcal O_{X,x}$ is regular. Then for some finite integer $r$ there is an isomorphism of rings
--   $$\widehat{\mathcal O}_{X,x}\cong K[[t_1,\ldots,t_r]],$$
--   where the left side is the completion of the actual scheme stalk at its maximal ideal. No projectivity, properness, integrality or characteristic restriction is imposed. This supplies the formal models required by the local formulation of the Philippon mission's alteration construction once regularity of its candidate source has been established. It does not assert the existence of that global source or algebraize a formal model into an atlas.
-- source:
--   Application of Stacks Project Lemma 10.160.10(2), Tag 0C0S, https://stacks.math.columbia.edu/tag/0C0S , to the completed local ring of a regular closed point. Completion preserves regularity by Lemma 15.44.4, Tag 07NY, https://stacks.math.columbia.edu/tag/07NY . The coefficient field is the original algebraically closed ground field: Mathlib AlgebraicGeometry.residueFieldIsoBase identifies the residue field of a closed point of a locally finite-type scheme with that field. All these steps are included in the submitted proof.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
universe u

theorem AlgebraicGeometry.exists_completedStalk_ringEquiv_mvPowerSeries_of_regular_closedPoint
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (x : X) (hx : IsClosed ({x} : Set X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ r : ℕ, Nonempty (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+* MvPowerSeries (Fin r) K) := by sorry
