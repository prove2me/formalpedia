-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap
-- name    : AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/60fff23f-6279-57c8-bbcf-fb8c08c79743
-- title:
--   Zariski-local-at-target properties pass to coproducts of morphisms
-- statement:
--   Let $P$ be a property of morphisms of schemes (a `MorphismProperty Scheme.{u}`) which is local at the target for the Zariski topology, in the sense of Mathlib's `IsZariskiLocalAtTarget`. Let $\sigma$ be an index type in the same universe, let $X, Y : \sigma \to$ `Scheme.{u}` be $\sigma$-indexed families of schemes, and let $f$ assign to each $i \in \sigma$ a morphism $f_i : X_i \to Y_i$. Assume that $f_i$ satisfies $P$ for every $i$. The conclusion is that the morphism `Limits.Sigma.map f`, the coproduct morphism $\coprod_i X_i \to \coprod_i Y_i$ induced by the family $(f_i)$ in the category of schemes, satisfies $P$. This is the $\sigma$-indexed analogue of the binary statement that a property local at the target is stable under taking the coproduct of two morphisms; no finiteness or nonemptiness assumption is placed on the index type $\sigma$.
--
--   The statement records that any property of scheme morphisms which is Zariski-local on the target — for instance being a closed immersion, separated, proper, quasi-compact or affine — is inherited by an arbitrary coproduct of morphisms. It is used in the construction of morphisms out of coproducts of schemes in the Hilbert-polynomial stratification argument, where a scheme over a clopen decomposition of the base is exhibited as a coproduct of pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by sorry
