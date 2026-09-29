-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_opens_nonempty_subset_image_of_apply_genericPoint_eq
-- name    : AlgebraicGeometry.exists_opens_nonempty_subset_image_of_apply_genericPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ae7d662d-0305-59fd-9185-a766a041b3b2
-- title:
--   Image of a non-empty open under a dominant morphism contains a non-empty open
-- statement:
--   Let $f : X \to Y$ be a morphism of schemes which is locally of finite presentation and quasi-compact, with the underlying topological space of $Y$ compact and quasi-separated, and with the underlying spaces of both $X$ and $Y$ irreducible. Assume $f$ is dominant in the strong sense that the induced map on points sends the generic point of $X$ to the generic point of $Y$, i.e. $f.base(\xi_X) = \xi_Y$. Then for every open subscheme $U$ of $X$ whose underlying set is non-empty, there exists an open $V$ of $Y$ whose underlying set is non-empty and satisfies $V \subseteq f.base(U)$, the set-theoretic image of the underlying set of $U$ under the map on points. Thus the image of any non-empty open of $X$ has non-empty interior; no assertion is made that $V$ can be taken inside a prescribed open of $Y$, nor that $f(U)$ itself is open or constructible.
--
--   This is the standard consequence of Chevalley's theorem on images of constructible sets (EGA IV 1.8.4): a dominant morphism of finite presentation between irreducible schemes has image of each non-empty open containing a non-empty open, so such images are "dense up to shrinking". In this development it supplies the density statements for the sets of points of the Čerednik–Drinfel'd constructions where a place factors suitably through a degeneracy map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_opens_nonempty_subset_image_of_apply_genericPoint_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Topology

universe u

theorem AlgebraicGeometry.exists_opens_nonempty_subset_image_of_apply_genericPoint_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace ↥Y] [QuasiSeparatedSpace ↥Y] [IrreducibleSpace ↥X] [IrreducibleSpace ↥Y]
    (hdom : f.base (genericPoint ↥X) = genericPoint ↥Y)
    (U : X.Opens) (hU : (U : Set ↥X).Nonempty) :
    ∃ V : Y.Opens, (V : Set ↥Y).Nonempty ∧ (V : Set ↥Y) ⊆ f.base '' (U : Set ↥X) := by sorry
