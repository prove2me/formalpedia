-- Prove2me | Theorems.Thm_Algebra_exists_weilRestriction_points_equiv_finiteType
-- name    : Algebra.exists_weilRestriction_points_equiv_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/667043c0-b134-5c74-b592-104cc70b091f
-- title:
--   Weil restriction along a finite free extension preserves finite type
-- statement:
--   Let $A$ and $B$ be commutative rings in a fixed universe, with $B$ an $A$-algebra that is finite and free as an $A$-module, and let $H$ be a commutative ring equipped with a $B$-algebra structure which makes it of finite type over $B$. The assertion is that there exist a type $W$ in the same universe, a commutative ring structure on $W$ and an $A$-algebra structure on it, such that $W$ is of finite type as an $A$-algebra, and moreover there is a family $e$ assigning to every commutative $A$-algebra $T$ a bijection
--   $$e_T : \operatorname{Hom}_{A\text{-alg}}(W, T) \xrightarrow{\ \sim\ } \operatorname{Hom}_{B\text{-alg}}(H, B \otimes_A T),$$
--   which is natural in $T$ in the following sense: for all commutative $A$-algebras $T$, $T'$, every $A$-algebra map $u : T \to T'$ and every $A$-algebra map $f : W \to T$, one has $e_{T'}(u \circ f) = (\mathrm{id}_B \otimes u) \circ e_T(f)$, where $\mathrm{id}_B \otimes u : B \otimes_A T \to B \otimes_A T'$ is the induced map on tensor products.
--
--   This is the affine Weil restriction $\operatorname{Res}_{B/A}\operatorname{Spec} H$ in functor-of-points form, with the additional conclusion that the representing $A$-algebra may be taken of finite type; it is used in the construction of Weil restrictions of affine schemes along finite free base extensions, via [`AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique`](thm.html#AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_weilRestriction_points_equiv_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_weilRestriction_points_equiv_finiteType
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [Algebra B H] [Algebra.FiniteType B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W), Algebra.FiniteType A W ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f) := by sorry
