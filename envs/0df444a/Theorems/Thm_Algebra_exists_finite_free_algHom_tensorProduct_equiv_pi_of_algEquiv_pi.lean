-- Prove2me | Theorems.Thm_Algebra_exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi
-- name    : Algebra.exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/cd6995a7-5759-5434-bfa4-a541469d69d8
-- title:
--   Split case of Weil restriction points: Hom_B(H,B⊗_A T)≅prodᵢHom_{A'}(Fᵢ,T)
-- statement:
--   Let $A$, $B$, $H$, $A'$ be commutative rings in a fixed universe, with $B$ an $A$-algebra, $H$ a $B$-algebra that is finite and free as a $B$-module, and $A'$ an $A$-algebra; let $d$ be a natural number and let $\varphi \colon A' \otimes_A B \to (A')^{d}$, indexed by `Fin d`, be an isomorphism of $A'$-algebras (so $B$ splits into $d$ factors after base change to $A'$). The conclusion asserts the existence of a family of types $F_i$ ($i \in$ `Fin d`) in the same universe, each equipped with a commutative ring structure and an $A'$-algebra structure, such that every $F_i$ is finite and free as an $A'$-module, together with a family $\sigma$ assigning to each commutative ring $T$ carrying an $A$-algebra structure and an $A'$-algebra structure which form a scalar tower over $A \to A'$ a bijection $$\sigma_T \colon \operatorname{Hom}_{B\text{-alg}}(H,\, B \otimes_A T) \;\xrightarrow{\ \sim\ }\; \prod_{i} \operatorname{Hom}_{A'\text{-alg}}(F_i,\, T),$$ subject to the following compatibility: for any two such $T$, $T'$, any $A'$-algebra map $u \colon T \to T'$ and any $B$-algebra map $g \colon H \to B \otimes_A T$, applying $\sigma_{T'}$ to $g$ followed by $\mathrm{id}_B \otimes u$ (the latter formed from $u$ regarded as an $A$-algebra map) gives the tuple whose $i$-th entry is $\sigma_T(g)_i$ followed by $u$. The algebras $F_i$ and the bijections are only asserted to exist; no description of them is part of the statement.
--
--   This is the split case of the computation of the points of a Weil restriction $\operatorname{Res}_{B/A}$ of a finite free $B$-algebra: once $B \otimes_A A'$ is a product of $d$ copies of $A'$, a $B$-algebra map $H \to B \otimes_A T$ is the same as a $d$-tuple of $A'$-algebra maps out of the base changes of $H$ along the $d$ characters of the splitting, functorially in $T$. It is used by [`Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi`](thm.html#Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi) to deduce finiteness and freeness properties of the representing algebras of such restrictions of scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (A' : Type u) [CommRing A'] [Algebra A A'] (d : ℕ) (φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')) :
    ∃ (F : Fin d → Type u) (_ : ∀ i, CommRing (F i)) (_ : ∀ i, Algebra A' (F i)),
      (∀ i, Module.Finite A' (F i)) ∧ (∀ i, Module.Free A' (F i)) ∧
      ∃ σ : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T],
          (H →ₐ[B] (B ⊗[A] T)) ≃ (∀ i, F i →ₐ[A'] T),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T]
          [CommRing T'] [Algebra A T'] [Algebra A' T'] [IsScalarTower A A' T'] (u : T →ₐ[A'] T')
          (g : H →ₐ[B] (B ⊗[A] T)),
          σ T' ((Algebra.TensorProduct.map (AlgHom.id B B) (u.restrictScalars A)).comp g)
            = fun i => u.comp (σ T g i) := by sorry
