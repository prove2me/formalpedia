-- Prove2me | Theorems.Thm_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace
-- name    : ArtinL.trace_restrict_invariants_eq_inv_card_mul_sum_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/c2e52e34-1c58-5d58-98f7-02fad3048b45
-- title:
--   Trace on invariants as average of traces over a finite subgroup
-- statement:
--   Let $K$ be a field of characteristic zero, $G$ a group, and $V$ a finite-dimensional $K$-vector space carrying a representation $\rho$ of $G$ (a `Representation K G V`, i.e. a homomorphism from $G$ to the $K$-linear automorphisms of $V$). Let $I \le G$ be a subgroup that is finite, and let $g \in G$. Write $W = V^{I}$ for the invariants of the composite of $\rho$ with the inclusion $I \hookrightarrow G$, i.e. the subspace of vectors fixed by $\rho(\tau)$ for all $\tau \in I$. Assume the hypothesis $h$ that $\rho(g)$ maps $W$ into itself: $\rho(g)v \in W$ for every $v \in W$. Then the trace over $K$ of the endomorphism of $W$ obtained by restricting $\rho(g)$ along $h$ equals $$\bigl(|I|\bigr)^{-1}\sum_{\tau \in I} \operatorname{tr}_{K}\bigl(\rho(g\tau) \colon V \to V\bigr),$$ where $|I|$ denotes the cardinality of $I$ viewed in $K$ (invertible because $K$ has characteristic zero and $I$ is nonempty), and the sum runs over all elements $\tau$ of the subgroup $I$.
--
--   This is the standard averaging identity expressing the trace of an operator on the space of invariants of a finite subgroup through the character of the whole representation. It is used in the computation of local Euler factors of Artin representations, where $I$ is an inertia subgroup and $g$ a Frobenius lift, and it is cited by [`ArtinL.codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom`](thm.html#ArtinL.codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom) and by [`ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.trace_restrict_invariants_eq_inv_card_mul_sum_trace
    {K : Type*} [Field K] [CharZero K] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G) [Fintype ↥I]
    (g : G)
    (h : ∀ v ∈ Representation.invariants (ρ.comp I.subtype),
      ρ g v ∈ Representation.invariants (ρ.comp I.subtype)) :
    LinearMap.trace K _ ((ρ g).restrict h) =
      (Fintype.card ↥I : K)⁻¹ * ∑ τ : ↥I, LinearMap.trace K V (ρ (g * τ)) := by sorry
