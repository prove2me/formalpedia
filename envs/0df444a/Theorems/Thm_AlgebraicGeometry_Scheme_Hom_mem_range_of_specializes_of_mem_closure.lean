-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_mem_range_of_specializes_of_mem_closure
-- name    : AlgebraicGeometry.Scheme.Hom.mem_range_of_specializes_of_mem_closure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/9bfc9932-6bce-58c0-bb91-40215d3bdc4e
-- title:
--   Quasi-compact finite-type morphisms hit accumulated generic points
-- statement:
--   Let $\Gamma$ and $G$ be schemes and let $\pi \colon \Gamma \to G$ be a morphism which is quasi-compact and locally of finite type, with $G$ locally Noetherian. Let $S$ be a subset of the underlying topological space of $G$ which is closed, and let $\eta$ be a point of $G$ lying in $S$ such that $\eta \leadsto x$ for every $x \in S$, i.e. every point of $S$ lies in the closure of $\{\eta\}$ (so $S$ is irreducible with generic point $\eta$). Let $D$ be a further subset of the space of $G$ with $D \subseteq S$, with $\eta$ in the closure of $D$, and with $D$ contained in the image of the map on points $\pi_{\mathrm{base}} \colon \Gamma \to G$ induced by $\pi$. The conclusion is that $\eta$ itself lies in the image of $\pi_{\mathrm{base}}$: the generic point of $S$ is hit by $\pi$ as soon as a set of points of $S$ in the image accumulates at it.
--
--   This is the topological core of the standard argument that the image of a quasi-compact morphism locally of finite type onto a locally Noetherian base is closed under passing from a dense set of points of an irreducible closed subset to its generic point; it is the point at which quasi-compactness of $\pi$ is needed. It is used in the construction of an extension over an open neighbourhood from a dense family of pointwise extensions, [`AlgebraicGeometry.Scheme.exists_opens_extension_of_pointwise_extension_dense`](thm.html#AlgebraicGeometry.Scheme.exists_opens_extension_of_pointwise_extension_dense).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_mem_range_of_specializes_of_mem_closure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.mem_range_of_specializes_of_mem_closure
    {Γ G : Scheme.{u}} (π : Γ ⟶ G) [QuasiCompact π] [LocallyOfFiniteType π] [IsLocallyNoetherian G]
    (S : Set G) (hS : IsClosed S) (η : G) (hηS : η ∈ S) (hirr : ∀ x ∈ S, η ⤳ x)
    (D : Set G) (hDS : D ⊆ S) (hDη : η ∈ closure D) (hDπ : D ⊆ Set.range π.base) :
    η ∈ Set.range π.base := by sorry
