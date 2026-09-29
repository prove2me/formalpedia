-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq
-- name    : ExtCitation.LocalLevel.mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/a709a999-3da7-52cb-93e7-8fe81cb87c11
-- title:
--   Fixed field of N∩ S lies in a cyclotomic layer over K'
-- statement:
--   Let $q$ be a prime and let $L$ be an intermediate field of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$ (the algebraic closure being `PadicAlgCl q`) that is finite-dimensional over $\mathbb{Q}_q$. Let $G$ be a finite group acting on $L$ by ring automorphisms, the action being faithful and fixing the image of $\mathbb{Q}_q$ pointwise (hypothesis `hG`). Let $S \le G$ be a subgroup, and let $K'$ be a further intermediate field, finite-dimensional over $\mathbb{Q}_q$ and contained in $L$, which is exactly the $S$-fixed subfield of $L$: for $x \in L$ one has $x \in K'$ if and only if $s \cdot x = x$ for all $s \in S$. Let $N \trianglelefteq G$ be a normal subgroup, and suppose given $\pi \in L$ fixed by every element of $G$, with $\|\pi\| < 1$, and of maximal norm among $N$-fixed elements of norm $< 1$: every $y \in L$ fixed by all $n \in N$ with $\|y\| < 1$ satisfies $\|y\| \le \|\pi\|$. The conclusion asserts the existence of an integer $N_0 > 0$ such that every $x \in L$ fixed by all elements of $N \sqcap S$ lies in `IntermediateField.adjoin K'` applied to the set of $\zeta \in \overline{\mathbb{Q}}_q$ with $\zeta^{q^{N_0}-1} = 1$.
--
--   This is the relative form of the statement that unramified extensions of a $q$-adic field are cyclotomic: the field fixed by $N \cap S$ is contained in $K'(\mu_{q^{N_0}-1})$ for a suitable $N_0$, the hypotheses on $\pi$ encoding that $N$ is an unramified level. It feeds into [`ExtCitation.LocalLevel.exists_frobenius_uniformiser_inf_level`](thm.html#ExtCitation.LocalLevel.exists_frobenius_uniformiser_inf_level), and its proof invokes [`ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one`](thm.html#ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one), the criterion that an element of $G$ moving every $N$-fixed element of norm $\le 1$ by less than $1$ already lies in $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (π : L) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) →
      (x : PadicAlgCl q) ∈ IntermediateField.adjoin K' {ζ : PadicAlgCl q | ζ ^ (q ^ N₀ - 1) = 1} := by sorry
