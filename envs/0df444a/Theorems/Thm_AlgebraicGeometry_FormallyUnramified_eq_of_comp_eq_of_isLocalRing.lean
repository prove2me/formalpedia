-- Prove2me | Theorems.Thm_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing
-- name    : AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/717e6388-e51f-5b01-b972-d3e7660dac55
-- title:
--   Local-ring points of an unramified morphism agreeing at the closed point
-- statement:
--   Let $f : X \to Y$ be a morphism of schemes (in a fixed universe) which is formally unramified and locally of finite type, and let $O$ be a commutative local ring. Let $a, b : \operatorname{Spec}(O) \to X$ be two morphisms which become equal after composition with $f$, that is $f \circ a = f \circ b$. Suppose further that there is a scheme $T$ and a morphism $t : T \to \operatorname{Spec}(O)$ whose underlying continuous map has the closed point of the local ring $O$ in its set-theoretic image, and such that $a \circ t = b \circ t$. The conclusion is that $a = b$ as morphisms of schemes $\operatorname{Spec}(O) \to X$. Note that no hypothesis of separatedness or of finiteness on $O$ is imposed, and $t$ is not required to be a closed immersion, a monomorphism, or dominant: only that its image meets the closed point and that it equalises $a$ and $b$.
--
--   This is the uniqueness half of the statement that points of an unramified morphism are determined by their reductions: two $O$-points of $X$ lying over the same $O$-point of $Y$ and agreeing on any subscheme through the closed point of $\operatorname{Spec} O$ coincide (EGA IV 17.4.1). It is used in the construction of the relative group law on elliptic curves of good reduction, where it supplies uniqueness of a torsion point lifting a prescribed point of the reduction over a henselian local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_isLocalRing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (a b : Spec (CommRingCat.of O) ⟶ X) (hf : a ≫ f = b ≫ f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of O))
    (ht : IsLocalRing.closedPoint O ∈ Set.range t.base)
    (hab : t ≫ a = t ≫ b) : a = b := by sorry
