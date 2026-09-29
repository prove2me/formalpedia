-- Prove2me | Theorems.Thm_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk
-- name    : AlgebraicGeometry.Flat.isDomain_stalk_of_isDomain_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/b1ef2d62-6fb7-5672-9b7c-1c03f5a4822e
-- title:
--   Domain stalks descend along flat morphisms of schemes
-- statement:
--   Let $Y$ and $Z$ be schemes (in a fixed universe) and let $h \colon Y \to Z$ be a morphism of schemes which is flat, in the sense of Mathlib's `Flat` typeclass for scheme morphisms. Let $y$ be a point of $Y$, and suppose the stalk $\mathcal{O}_{Y,y}$ of the structure sheaf of $Y$ at $y$ is an integral domain (a nontrivial commutative ring without zero divisors, as expressed by `IsDomain`). The conclusion is that the stalk $\mathcal{O}_{Z,h(y)}$ of the structure sheaf of $Z$ at the image point $h(y)$ is likewise an integral domain. Thus the property of having domain local rings propagates from a point of the source to its image under a flat morphism; no finiteness, separatedness or surjectivity hypothesis on $h$ is imposed, and nothing is assumed about the other points of $Y$ or $Z$.
--
--   This is the standard descent of integrality of local rings along a flat morphism, a consequence of the injectivity of flat local homomorphisms of local rings. It is used in the analysis of the special fibre of an integral model of a modular curve, where passing from a geometric fibre to the fibre itself is a flat base change along a field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Flat.isDomain_stalk_of_isDomain_stalk
    {Y Z : Scheme.{u}} (h : Y ⟶ Z) [Flat h] (y : Y) [IsDomain (Y.presheaf.stalk y)] :
    IsDomain (Z.presheaf.stalk (h y)) := by sorry
