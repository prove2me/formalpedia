-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_mem_and_isIso_pullbackMap_opens_of_forall_exists_isIso_morphismRestrict
-- name    : AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_forall_exists_isIso_morphismRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/6be597cd-66b8-5be1-87be-c3bc78212cfb
-- title:
--   Isomorphism near a fibre spreads to an open neighbourhood of y
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in the bottom universe), let $p : Z \to Y$ and $q : X \to Y$ be morphisms, and let $h : Z \to X$ satisfy $h$ followed by $q$ equals $p$, so that $h$ is a morphism over $Y$. Assume $p$ and $q$ are each proper, flat and locally of finite presentation. Let $y$ be a point of $Y$ and suppose that for every point $x$ of $X$ whose image $q(x)$ is $y$ there is an open subscheme $D$ of $X$ with $x \in D$ such that the restriction $h \mid_D : h^{-1}(D) \to D$ of $h$ over $D$ is an isomorphism. The conclusion is that there exists an open $V$ of $Y$ with $y \in V$ such that the morphism $Z \times_Y V \to X \times_Y V$ induced by $h$ over the identity of $V$ — the map of pullbacks of $p$ and of $q$ along the inclusion $V \hookrightarrow Y$ given by $h$, the identity of $V$ and the identity of $Y$ — is an isomorphism.
--
--   This is the standard "tube lemma" spreading-out argument: an isomorphism along a proper fibre is an isomorphism over a neighbourhood of the base point, combining the closedness of a proper map with the fact that being an isomorphism is Zariski-local on the target. It feeds [`AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_isClosedImmersion_pullbackMap_opens`](thm.html#AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_isClosedImmersion_pullbackMap_opens), the hypotheses on $p$ and $q$ being those carried along by that consumer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_mem_and_isIso_pullbackMap_opens_of_forall_exists_isIso_morphismRestrict.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_forall_exists_isIso_morphismRestrict
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hD : ∀ x : X, q.base x = y → ∃ D : X.Opens, x ∈ D ∧ IsIso (h ∣_ D)) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by sorry
