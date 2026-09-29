-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective
-- name    : AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/bc9b913c-35c2-53c0-b29f-9674eff6ff02
-- title:
--   Effective descent from a flat surjective quasi-compact kernel pair
-- statement:
--   Fix schemes and morphisms $s \colon S' \to S$ and $x' \colon X' \to S'$, together with a descent action $A$ for $s$ on $x'$, that is, a morphism $A.\mathrm{act} \colon X' \times_S S' \to X'$ from the pullback of $x' \circ s$ along $s$ satisfying $A.\mathrm{act} \circ x' = \mathrm{pr}_2$ (in diagrammatic order, `A.act ≫ x'` is the second projection) together with the unit and cocycle identities recorded in `DescentAction`. Let $p \colon X' \to Y$ be flat, surjective and quasi-compact, assume $\mathrm{pr}_1$ followed by $p$ equals $A.\mathrm{act}$ followed by $p$, and assume moreover that the square with sides $\mathrm{pr}_1, A.\mathrm{act}$ over $p, p$ is cartesian, i.e. $(\mathrm{pr}_1, A.\mathrm{act}) \colon X' \times_S S' \to X' \times_Y X'$ is an isomorphism of kernel pairs. Finally let $f \colon Y \to S$ satisfy $p$ followed by $f$ equals $x'$ followed by $s$. The conclusion asserts the existence of an isomorphism $e \colon Y \times_S S' \xrightarrow{\sim} X'$ such that $e$ followed by $x'$ is the projection $Y \times_S S' \to S'$, such that $e^{-1}$ is the comparison morphism $(p, x') \colon X' \to Y \times_S S'$, and such that the morphism $(Y \times_S S') \times_S S' \to X' \times_S S'$ induced by $e$ and the identities of $S'$ and $S$, followed by $A.\mathrm{act}$, agrees with the canonical descent action `(DescentAction.canonical s f).act`, namely `DescentAction.flipMap s f`, followed by $e$.
--
--   This is the effectivity step of faithfully flat quasi-compact descent for schemes: a descent datum whose associated equivalence relation is realised as the kernel pair of a flat surjective quasi-compact morphism $p \colon X' \to Y$ is effective, with descended object $(Y, f)$, and the comparison morphism $(p,x')$ is an isomorphism compatible with the canonical descent action on the base change. It is used to descend finite étale quotients, in [`AlgebraicGeometry.DescentAction.effective_of_finiteEtale`](thm.html#AlgebraicGeometry.DescentAction.effective_of_finiteEtale) and [`AlgebraicGeometry.DescentAction.effective_of_finiteEtale_of_forall_orbit`](thm.html#AlgebraicGeometry.DescentAction.effective_of_finiteEtale_of_forall_orbit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
    {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x')
    {Y : Scheme.{u}} (p : X' ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    (w : pullback.fst (x' ≫ s) s ≫ p = A.act ≫ p)
    (hR : IsPullback (pullback.fst (x' ≫ s) s) A.act p p)
    (f : Y ⟶ S) (hpf : p ≫ f = x' ≫ s) :
    ∃ (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s),
      e.inv = pullback.lift p x' hpf ∧
      pullback.map (pullback.snd f s ≫ s) s (x' ≫ s) s e.hom (𝟙 S') (𝟙 S)
          (by rw [Category.comp_id, ← Category.assoc, he]) (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical s f).act ≫ e.hom := by sorry
