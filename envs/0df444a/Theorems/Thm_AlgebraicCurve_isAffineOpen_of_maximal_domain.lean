-- Prove2me | Theorems.Thm_AlgebraicCurve_isAffineOpen_of_maximal_domain
-- name    : AlgebraicCurve.isAffineOpen_of_maximal_domain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/0d59eb65-edac-501f-bf5b-8820512f3436
-- title:
--   Maximal domain of a transcendental function is affine
-- statement:
--   Let $k$ be a field, let $C$ be a scheme over $k$ by way of a morphism $c \colon C \to \operatorname{Spec} k$, and assume $C$ is integral and $c$ is proper and smooth of relative dimension $1$. Let $U$ be an open subset of $C$ whose underlying space is nonempty, and let $s \in \Gamma(C, U)$ be a section of the structure sheaf over $U$. Write $\bar s$ for the image of $s$ in the function field of $C$ under the germ map at the generic point. Two hypotheses are imposed on $s$: first, $U$ is the exact domain of regularity of $\bar s$ in the sense that for every point $x$ of $C$, if $\bar s$ lies in the image of the canonical map from the local ring $\mathcal O_{C,x}$ to the function field, then $x \in U$; second, $\bar s$ is transcendental over $k$, where $k$ acts on the function field through the ring homomorphism [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), namely the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism of $k$, the map on global sections induced by $c$, and the germ map at the generic point. The conclusion is that $U$ is an affine open subset of $C$.
--
--   This is the standard criterion producing affine opens on a proper smooth curve: the locus where a nonconstant rational function is regular is affine. It is used to prove that any finite set of points of such a curve is contained in an affine open, via [`AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset`](thm.html#AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isAffineOpen_of_maximal_domain.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicCurve.isAffineOpen_of_maximal_domain
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s)) :
    IsAffineOpen U := by sorry
