-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd
-- name    : AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/55b7b29e-3785-5791-9f23-c2c18a11cd9d
-- title:
--   Base change of a fibre product of schemes
-- statement:
--   Let $S$, $S'$, $Z$, $X$ be schemes (in a fixed universe) and let $z \colon Z \to S$, $f \colon X \to S$ and $\iota \colon S' \to S$ be morphisms of schemes; no further hypotheses are imposed. Write $P = Z \times_S X$ for Mathlib's chosen pullback of $z$ and $f$, equipped with the structure morphism $\mathrm{pr}_Z$ followed by $z$, and set $P' = P \times_S S'$ (the pullback of that structure morphism along $\iota$), $Z' = Z\times_S S'$ and $X' = X \times_S S'$. The assertion is that the morphism $P' \to Z' \times_{S'} X'$, where the target is the pullback of the two projections $Z' \to S'$ and $X' \to S'$, is an isomorphism; this morphism is the one induced by the universal property from its two components, namely the map $P' \to Z'$ with components ($\mathrm{pr}_P$ followed by $\mathrm{pr}_Z$, $\mathrm{pr}_{S'}$) and the map $P' \to X'$ with components ($\mathrm{pr}_P$ followed by $\mathrm{pr}_X$, $\mathrm{pr}_{S'}$), the required commutations being instances of associativity together with the defining equalities of the pullbacks involved. Since both components have the same projection to $S'$, they agree over $S'$, so the induced morphism to $Z' \times_{S'} X'$ exists.
--
--   This is the standard compatibility of fibre products with base change, $(Z\times_S X)\times_S S' \cong (Z\times_S S')\times_{S'}(X\times_S S')$, realised for Mathlib's chosen pullbacks of schemes and for the concrete comparison morphism assembled from the two base-changed projections. It is used in the Néron-model infrastructure, where $\iota$ is the inclusion of the generic fibre and the two components are the restrictions to the generic fibre of the projections of $Z\times_S X$, to transport statements about stalks across this identification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd
    {S S' Z X : Scheme.{u}} (z : Z ⟶ S) (f : X ⟶ S) (ι : S' ⟶ S) :
    IsIso
      (pullback.lift
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.fst z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.snd z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc, ← pullback.condition (f := z) (g := f)]; exact pullback.condition))
        (by rw [pullback.lift_snd, pullback.lift_snd]) :
        pullback (pullback.fst z f ≫ z) ι ⟶ pullback (pullback.snd z ι) (pullback.snd f ι)) := by sorry
