-- Prove2me | Theorems.Thm_AddTorsor_bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ
-- name    : AddTorsor.bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/4e6e55b3-88c4-5130-8b09-f075b4fc0262
-- title:
--   Equivariant injection of a torsor into a pretransitive set
-- statement:
--   Let $k$ be a field, let $V$ and $W$ be $k$-vector spaces with $W$ finite-dimensional, and let $\tau : V \to W$ be a $k$-linear map. Let $L_A$ be an additive torsor under $V$ (in particular nonempty) and let $L_G$ be a set carrying an additive action of $W$ that is pretransitive, i.e. any point of $L_G$ is obtained from any other by translation by some element of $W$. Let $f : L_A \to L_G$ be an injective map which is equivariant along $\tau$, in the sense that $f(v +_v a) = \tau(v) +_v f(a)$ for all $v \in V$ and $a \in L_A$. Suppose further that there is a finite-dimensional $k$-subspace $U \subseteq V$ with $\operatorname{finrank}_k W \le \operatorname{finrank}_k U$. Then $\tau$ is bijective and $f$ is surjective. No finiteness is assumed of $V$ itself, and the dimension hypothesis enters only through the subspace $U$; the conclusion asserts bijectivity of $\tau$ on all of $V$, not merely on $U$.
--
--   This is the counting step in a dévissage of the kind used for Serre–Tate theory: when lifts of an object form a torsor under a linear space and lifts of an associated object form a set with a transitive action, an injective equivariant comparison map together with a dimension inequality forces both the linear comparison map and the comparison of lift sets to be bijective. It is cited in the construction of formal coordinates for bare deformations, [`GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddTorsor_bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w x y

theorem AddTorsor.bijective_and_surjective_of_vadd_eq_of_injective_of_finrank_le_univ
    {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V] {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (τ : V →ₗ[k] W)
    {LA : Type x} [AddTorsor V LA] {LG : Type y} [AddAction W LG] [AddAction.IsPretransitive W LG]
    (f : LA → LG) (hf : ∀ (v : V) (a : LA), f (v +ᵥ a) = τ v +ᵥ f a) (hinj : Function.Injective f)
    (U : Submodule k V) [FiniteDimensional k ↥U] (hdim : Module.finrank k W ≤ Module.finrank k ↥U) :
    Function.Bijective τ ∧ Function.Surjective f := by sorry
