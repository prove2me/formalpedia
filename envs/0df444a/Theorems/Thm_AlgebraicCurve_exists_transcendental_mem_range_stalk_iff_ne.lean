-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne
-- name    : AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/c449194c-0703-5fee-a2fc-b2a5050e5bad
-- title:
--   A function regular exactly away from one closed point
-- statement:
--   Let $K$ be an algebraically closed field and let $C$ be a scheme equipped with a morphism $c \colon C \to \operatorname{Spec} K$, with $C$ integral, $c$ separated and $c$ smooth of relative dimension $1$. Let $Q$ be a point of $C$ whose singleton $\{Q\}$ is closed. Regard the function field $C.\mathrm{functionField}$, i.e. the stalk of the structure sheaf at the generic point of $C$, as a $K$-algebra through the ring homomorphism [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), which is the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism of $K$ followed by the map on global sections induced by $c$ followed by the germ map at the generic point. The assertion is that there exists an element $f$ of the function field which is transcendental over $K$ and which has the property that, for every point $x$ of $C$, $f$ lies in the range of the canonical map from the stalk $\mathcal{O}_{C,x}$ into the function field if and only if $x \neq Q$. Thus $f$ is regular at every point of $C$ other than $Q$, and not regular at $Q$.
--
--   This is the standard existence statement, obtained classically from Riemann's inequality, of a rational function on a smooth separated curve over an algebraically closed field whose only pole is a prescribed closed point. It is used to produce affine open neighbourhoods avoiding a given finite set of points, in [`AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset`](thm.html#AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (Q : C) (hQ : IsClosed ({Q} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ f : C.functionField, Transcendental K f ∧
      ∀ x : C, f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range ↔ x ≠ Q := by sorry
