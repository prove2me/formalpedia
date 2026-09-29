-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_smooth_of_subsingleton_of_isAlgClosed
-- name    : AlgebraicGeometry.isIso_of_smooth_of_subsingleton_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/6402bb15-8305-5f94-95e2-5400c7356234
-- title:
--   A smooth k-scheme with a unique k-point is Spec k
-- statement:
--   Let $k$ be an algebraically closed field, viewed as an object of `CommRingCat`, and let $g : G \to \operatorname{Spec} k$ be a morphism of schemes (all in universe $0$) which is smooth. Assume $g$ admits a section, that is, a morphism $s : \operatorname{Spec} k \to G$ with $s$ followed by $g$ equal to the identity of $\operatorname{Spec} k$, and assume this section is the only one: every $s' : \operatorname{Spec} k \to G$ with $s'$ followed by $g$ equal to the identity of $\operatorname{Spec} k$ satisfies $s' = s$. Then $g$ is an isomorphism of schemes, so that $s$ is its inverse and $G \cong \operatorname{Spec} k$. In other words, a smooth scheme over an algebraically closed field whose set of $k$-rational points is a singleton is the one-point scheme $\operatorname{Spec} k$; the hypothesis is exactly that the section set is nonempty and has at most one element, stated via a distinguished section and a uniqueness clause rather than as a `Subsingleton` on $G(k)$ together with nonemptiness.
--
--   This is the scheme-theoretic rigidity statement that a smooth $k$-scheme, $k$ algebraically closed, with exactly one $k$-point must be trivial; smoothness enters only through 'locally of finite type and reduced'. It is used in the treatment of polarisations, where it yields triviality of a kernel from the statement that all its points of the relevant kind are the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_smooth_of_subsingleton_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_smooth_of_subsingleton_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [Smooth g]
    (s : Spec (CommRingCat.of k) ⟶ G) (hs : s ≫ g = 𝟙 _)
    (huniq : ∀ s' : Spec (CommRingCat.of k) ⟶ G, s' ≫ g = 𝟙 _ → s' = s) :
    IsIso g := by sorry
