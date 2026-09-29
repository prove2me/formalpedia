-- Prove2me | Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
-- name    : AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/62c0598c-3c6f-54a9-bfb9-2eb9d0cf1e73
-- title:
--   Finite surjective k-morphisms preserve fibre Krull dimension
-- statement:
--   Let $k$ be a field and let $X$ and $Y$ be schemes, together with morphisms $f : X \to \operatorname{Spec}(k)$ and $g : Y \to \operatorname{Spec}(k)$ and a morphism $p : X \to Y$ satisfying $g \circ p = f$ (written $p \gg g = f$, i.e. $p$ followed by $g$ equals $f$), where $p$ is assumed finite and surjective as a morphism of schemes. Let $s$ be a point of the underlying topological space of $\operatorname{Spec}(k)$. The conclusion is an equality of topological Krull dimensions of the two set-theoretic fibres over $s$, each regarded as a subspace: the Krull dimension of the subspace $g_{\mathrm{base}}^{-1}(\{s\})$ of $Y$ equals the Krull dimension of the subspace $f_{\mathrm{base}}^{-1}(\{s\})$ of $X$, where the topological Krull dimension is the supremum of lengths of strictly increasing chains of irreducible closed subsets. Since $\operatorname{Spec}(k)$ has exactly one point, these fibres are all of $Y$ and all of $X$, so the assertion is that $\dim Y = \dim X$ for the underlying spaces.
--
--   This is the standard invariance of (topological) Krull dimension under a finite surjective morphism, stated fibrewise over the base field, the shape in which relative dimension data are recorded in the quaternionic moduli part of the development. It is used in the construction of quotients of fake elliptic curves by finite flat stable subgroup schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective.lean

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.KrullDimension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (p : X ⟶ Y) (hp : p ≫ g = f) [IsFinite p] [Surjective p]
    (s : ↥(Spec (CommRingCat.of k))) :
    topologicalKrullDim ↥(g.base ⁻¹' {s}) = topologicalKrullDim ↥(f.base ⁻¹' {s}) := by sorry
