-- Prove2me | Theorems.Thm_Algebra_IsInvariant_exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq
-- name    : Algebra.IsInvariant.exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/719a6226-f2c0-5b7b-a1e6-a73613f5024c
-- title:
--   Invariants under a transitive action on maximal ideals form a local ring
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $G$ be a finite group acting on $B$ by ring automorphisms in a way compatible with the $A$-action (the $G$-action and the $A$-action on $B$ commute). Assume that the extension is invariant in the sense that every element of $B$ fixed by all of $G$ lies in the image of $A$ (`Algebra.IsInvariant A B G`), that $B$ is integral over $A$, and that the structure map $A \to B$ is faithful, i.e. injective. Let $\mathfrak P \subseteq B$ be a maximal ideal, and suppose the $G$-action is transitive on maximal ideals in the strong sense that every maximal ideal $Q$ of $B$ is of the form $g \bullet \mathfrak P$ for some $g \in G$. The conclusion asserts the existence of a local-ring structure on $A$ (i.e. $A$ is nontrivial with a unique maximal ideal) for which the maximal ideal of $A$ equals the contraction $\mathfrak P \cap A$, that is, the preimage `Ideal.under A 𝔓` of $\mathfrak P$ along $A \to B$.
--
--   This is the classical statement that the base of a finite-group-invariant integral extension is local as soon as the group permutes the maximal ideals of the upper ring transitively; here the locality witness is produced together with the identification of the maximal ideal as the contraction of $\mathfrak P$. It is used in the construction of local subalgebras from fixed points of inertia and in the analysis of the local ring of a node on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsInvariant_exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Pointwise

theorem Algebra.IsInvariant.exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [Algebra.IsIntegral A B] [FaithfulSMul A B]
    (𝔓 : Ideal B) [𝔓.IsMaximal]
    (htrans : ∀ Q : Ideal B, Q.IsMaximal → ∃ g : G, Q = g • 𝔓) :
    ∃ _ : IsLocalRing A, IsLocalRing.maximalIdeal A = Ideal.under A 𝔓 := by sorry
