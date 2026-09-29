-- Prove2me | Theorems.Thm_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation
-- name    : Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/cca2f81a-3909-5db0-b332-aacc077cec06
-- title:
--   Descent of finite type along faithfully flat finitely presented algebras
-- statement:
--   Let $R$, $A$ and $B$ be commutative rings, equipped with $R$-algebra structures on $A$ and on $B$ and an $A$-algebra structure on $B$, these being compatible in the sense that they form a scalar tower $R \to A \to B$ (the rings lie in three independent universes). Assume that $B$ is faithfully flat as an $A$-module, that $B$ is of finite presentation as an $A$-algebra, and that $B$ is of finite type as an $R$-algebra. Then $A$ is of finite type as an $R$-algebra, i.e. $A$ is generated as an $R$-algebra by finitely many elements. Thus the finite-type property of the composite $R \to B$ descends to the first factor $R \to A$ across a faithfully flat map of finite presentation $A \to B$; note that $B$ is only assumed of finite presentation over $A$ and of finite type (not finite presentation) over $R$.
--
--   This is the affine form of the assertion that "locally of finite type" is local on the source for the fppf topology: finite type descends along flat, surjective, finitely presented ring maps. It is used in the project to derive the corresponding descent of finite presentation, the descent of the property of being locally of finite presentation for morphisms of schemes, and finiteness statements for Hopf-Galois extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FiniteType R B] :
    Algebra.FiniteType R A := by sorry
