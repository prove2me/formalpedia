-- Prove2me | Theorems.Thm_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
-- name    : AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/4cd21eae-e71b-5934-99d2-40ca11556ec4
-- title:
--   Rigidity of maps from a formally unramified algebra
-- statement:
--   Let $R$ be a commutative ring and let $A$ be a commutative $R$-algebra which is essentially of finite type over $R$ (`Algebra.EssFiniteType`) and formally unramified over $R$ (`Algebra.FormallyUnramified`). Let $B$ be a further commutative $R$-algebra and let $I$ be an ideal of $B$ contained in the Jacobson radical of $B$, i.e. $I \le \mathrm{jacobson}(\bot)$, the intersection of the maximal ideals of $B$. Let $f, g \colon A \to B$ be two $R$-algebra homomorphisms such that $f(a) - g(a) \in I$ for every $a \in A$. Then $f = g$ as $R$-algebra homomorphisms. Thus two $R$-algebra maps out of an essentially finite type, formally unramified $R$-algebra that agree modulo an ideal contained in the Jacobson radical agree on the nose; no completeness, henselianity or nilpotence hypothesis on $I$ is imposed beyond $I \le \mathrm{jacobson}(\bot)$.
--
--   This is the standard rigidity (uniqueness of liftings) property of unramified morphisms, in the form where the ideal modulo which the two sections agree is only assumed to lie in the Jacobson radical rather than to be nilpotent or to define a complete topology. It is used in this development to pin down algebra and bialgebra homomorphisms after base change and to show that elements of an inertia subgroup act trivially on a formally unramified algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {B : Type w} [CommRing B] [Algebra R B]
    (I : Ideal B) (hI : I ≤ Ideal.jacobson ⊥)
    (f g : A →ₐ[R] B) (hfg : ∀ a : A, f a - g a ∈ I) :
    f = g := by sorry
