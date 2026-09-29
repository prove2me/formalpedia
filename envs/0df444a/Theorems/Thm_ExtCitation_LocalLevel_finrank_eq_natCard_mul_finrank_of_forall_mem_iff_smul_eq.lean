-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
-- name    : ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/ae0f63dd-39b9-5ac9-83b2-2c5a263c6e12
-- title:
--   Degree of a faithful layer: [L:ℚ_q]=|G| [K:ℚ_q]
-- statement:
--   Fix a prime $q$ and work inside a fixed algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$. Let $L$ be an intermediate field of $\mathbb{Q}_q \subseteq$ `PadicAlgCl q` that is finite-dimensional over $\mathbb{Q}_q$, and let $G$ be a finite group acting on $L$ by ring automorphisms (a `MulSemiringAction`), the action being faithful. Assume moreover that $G$ fixes the base pointwise: $g \cdot \iota(x) = \iota(x)$ for every $g \in G$ and every $x \in \mathbb{Q}_q$, where $\iota$ is the structure map $\mathbb{Q}_q \to L$; so $G$ acts by $\mathbb{Q}_q$-algebra automorphisms. Let $K$ be a further intermediate field of $\mathbb{Q}_q \subseteq$ `PadicAlgCl q` with $K \le L$, and suppose that $K$ cuts out exactly the invariants of $G$ inside $L$: for every $x \in L$, the image of $x$ in `PadicAlgCl q` lies in $K$ if and only if $g \cdot x = x$ for all $g \in G$. The conclusion is the degree identity $\operatorname{finrank}_{\mathbb{Q}_q} L = |G| \cdot \operatorname{finrank}_{\mathbb{Q}_q} K$, with $|G|$ the cardinality of $G$ as a natural number.
--
--   This is Artin's theorem on fixed fields, $[L:L^G] = |G|$, combined with the tower law, in the form needed for layers of local extensions: the hypothesis on $K$ identifies it with the field of $G$-invariants of $L$. It is used in the local analysis of the extensions cut out by residual representations, for instance by [`ExtCitation.LocalLevel.eq_of_unramified_level_of_index_eq`](thm.html#ExtCitation.LocalLevel.eq_of_unramified_level_of_index_eq), [`ExtCitation.LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow`](thm.html#ExtCitation.LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow) and [`ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic`](thm.html#ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic), where applying it to a subgroup and dividing converts relative degrees into group indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x) :
    Module.finrank ℚ_[q] L = Nat.card G * Module.finrank ℚ_[q] K := by sorry
