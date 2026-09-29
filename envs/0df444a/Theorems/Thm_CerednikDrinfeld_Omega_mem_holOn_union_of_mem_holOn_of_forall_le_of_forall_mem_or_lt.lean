-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
-- name    : CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/3c2dfc33-6f9c-5eaf-8f75-e9ec366c2516
-- title:
--   Gluing holomorphic functions across a sphere
-- statement:
--   Let $K$ be an algebraically closed field carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $S_1, S_2 \subseteq K$ be subsets, let $t_0, \pi_0 \in K$ with $\pi_0 \neq 0$, and let $Z \subseteq K$ be a finite set. Assume: every $z \in S_1$ satisfies $v(\pi_0) \le v(z - t_0)$, so $S_1$ avoids the open disc of radius $v(\pi_0)$ about $t_0$; every $z \in S_2$ either lies in $S_1$ or satisfies $v(z - t_0) < v(\pi_0)$; and every $z$ on the sphere $v(z - t_0) = v(\pi_0)$ with $v(\pi_0) \le v(z - \zeta)$ for all $\zeta \in Z$ lies in $S_1 \cap S_2$. Let $h : S_1 \cup S_2 \to K$ be a function whose restriction along each of the two inclusions belongs to `holOn`, that is, on $S_1$ (and likewise on $S_2$) there is a sequence of rational pairs $r_k$, each pole-free on the set, with a single $b \in K$ bounding $v(r_k(z)) \le v(b)$ for all $k$ and all points of the set, and with $r_k$ converging uniformly on the set to the restriction of $h$. The conclusion is that $h$ itself belongs to `holOn K (S₁ ∪ S₂)`, i.e. is a uniformly bounded uniform limit on $S_1 \cup S_2$ of rational pairs pole-free there.
--
--   This is the two-piece gluing (sheaf) property for rigid-analytic functions, here in the elementary form of uniform approximation by bounded pole-free rational functions, with the two pieces separated by the sphere $v(z-t_0)=v(\pi_0)$ up to finitely many excluded residue discs indexed by $Z$. It is the basic step behind the gluing lemmas for half-disc pieces, for linear pieces and for chains of pieces used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S₁ S₂ : Set K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) (Z : Finset K)
    (h₁ : ∀ z ∈ S₁, Valued.v π₀ ≤ Valued.v (z - t₀))
    (h₂ : ∀ z ∈ S₂, z ∈ S₁ ∨ Valued.v (z - t₀) < Valued.v π₀)
    (hC : ∀ z : K, Valued.v (z - t₀) = Valued.v π₀ → (∀ ζ ∈ Z, Valued.v π₀ ≤ Valued.v (z - ζ)) → z ∈ S₁ ∩ S₂)
    (h : ↥(S₁ ∪ S₂) → K)
    (hh₁ : (fun z : ↥S₁ => h ⟨(z : K), Or.inl z.2⟩) ∈ holOn K S₁)
    (hh₂ : (fun z : ↥S₂ => h ⟨(z : K), Or.inr z.2⟩) ∈ holOn K S₂) :
    h ∈ holOn K (S₁ ∪ S₂) := by sorry
