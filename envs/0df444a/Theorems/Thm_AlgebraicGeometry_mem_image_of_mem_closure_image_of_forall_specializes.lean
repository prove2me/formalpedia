-- Prove2me | Theorems.Thm_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes
-- name    : AlgebraicGeometry.mem_image_of_mem_closure_image_of_forall_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/c699f5b9-5344-5011-b883-6b220551db72
-- title:
--   Constructible sets contain generising points of their image's closure
-- statement:
--   Let $f\colon X \to Y$ be a morphism of schemes (over a fixed universe) which is locally of finite presentation and quasi-compact, and suppose the underlying space of $Y$ is compact and quasi-separated. Let $C \subseteq X$ be a subset of the underlying topological space of $X$ that is constructible in the sense of `Topology.IsConstructible`, and let $y$ be a point of $Y$ such that, first, $y$ lies in the closure of the image $f(C)$ of $C$ under the continuous map $f$ on underlying spaces, and second, $y$ specialises to $f(c)$ for every $c \in C$, that is, each $f(c)$ lies in the closure of $\{y\}$, so that $y$ generises every point of $f(C)$. The conclusion is that $y$ itself belongs to $f(C)$, i.e. $y = f(c)$ for some $c \in C$. Note that the assertion is about membership in the image of $C$, not in $C$ itself, and that the hypotheses on $f$ and on the space of $Y$ serve only to guarantee that $f(C)$ is again constructible.
--
--   This is the combination of Chevalley's theorem on the constructibility of images under morphisms locally of finite presentation with the fact that a constructible set contains any point of its closure which generises all of its points. It is used in the Néron model infrastructure, in the nowhere-density step establishing that a point of the special fibre admitting no extension of sections lies outside a suitable closure of a first projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology

universe u

theorem AlgebraicGeometry.mem_image_of_mem_closure_image_of_forall_specializes
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {C : Set X} (hC : Topology.IsConstructible C)
    {y : Y} (hy : y ∈ closure (f.base '' C)) (hgen : ∀ c ∈ C, y ⤳ f.base c) :
    y ∈ f.base '' C := by sorry
