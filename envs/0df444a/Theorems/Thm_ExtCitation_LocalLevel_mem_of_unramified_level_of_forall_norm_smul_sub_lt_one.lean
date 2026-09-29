-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
-- name    : ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/acb2a230-dfe3-5fc1-9ca6-6115513eb345
-- title:
--   Triviality of inertia at an unramified level
-- statement:
--   Let $q$ be a prime and let $L$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ (the fixed algebraic closure `PadicAlgCl q`) that is finite-dimensional over $\mathbb{Q}_q$. Let $G$ be a finite group acting on $L$ by ring and multiplicative automorphisms, the action being faithful and fixing every element of the image of $\mathbb{Q}_q$ in $L$, and let $N$ be a normal subgroup of $G$. Suppose $\pi \in L$ is fixed by every element of $G$, has $\|\pi\| < 1$ for the absolute value of $\overline{\mathbb{Q}}_q$, and is of maximal absolute value among the elements of norm $< 1$ fixed by $N$: every $y \in L$ with $n \cdot y = y$ for all $n \in N$ and $\|y\| < 1$ satisfies $\|y\| \le \|\pi\|$. Let $g \in G$ be such that for every $x \in L$ fixed by all of $N$ with $\|x\| \le 1$ one has $\|g \cdot x - x\| < 1$. Then $g \in N$.
--
--   The hypotheses on $\pi$ say that a uniformiser of the $N$-fixed subfield already lies in the $G$-fixed subfield, i.e. that the level $L^N$ is unramified over $L^G$; the conclusion is the triviality of the inertia subgroup there, equivalently the faithfulness of the action of $G/N$ on the residue field of $L^N$. It is used in the local analysis of unramified levels, for instance in identifying the Frobenius of a smaller level as a power of the Frobenius and in comparing ramification indices and inertia degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (N : Subgroup G) [N.Normal]
    (π : L) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖)
    (g : G) (hg : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((g • x : L) : PadicAlgCl q) - (x : PadicAlgCl q)‖ < 1) :
    g ∈ N := by sorry
