-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff
-- name    : ExtCitation.LocalLevel.algEquiv_apply_mem_Rw_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/14d5a1ce-4b36-516b-a8e9-79f45cbeeb9d
-- title:
--   ℚ_q-automorphisms of K_w preserve its ring of integers
-- statement:
--   Fix a natural number $q$ together with the assumption that $q$ is prime, and let `PadicAlgCl q` be the project's algebraic closure of $\mathbb{Q}_q$, equipped with its absolute value extending that of $\mathbb{Q}_q$. Let $K_w$ be an intermediate field of the extension `PadicAlgCl q`$/\mathbb{Q}_q$ which is finite-dimensional over $\mathbb{Q}_q$, let $\sigma : K_w \to K_w$ be an isomorphism of $K_w$ with itself as a $\mathbb{Q}_q$-algebra, and let $x \in K_w$. The assertion is the equivalence $\sigma(x) \in R_w \iff x \in R_w$, where $R_w$ denotes the project's subring `Rw q Kw` of $K_w$; its members are exactly those $x$ whose image in `PadicAlgCl q` has absolute value at most $1$, i.e. $R_w$ is the pullback to $K_w$ of the valuation subring of the algebraic closure. Thus the statement is the stability of $R_w$ under every $\mathbb{Q}_q$-automorphism of $K_w$, recorded as a membership equivalence for a single element rather than as the equality $\sigma(R_w)=R_w$ or as a group action on $R_w$.
--
--   This is the standard fact that the local Galois action on a finite extension $K_w$ of $\mathbb{Q}_q$ inside $\overline{\mathbb{Q}}_q$ restricts to the ring of integers. It is used in the local analysis at an auxiliary prime $w$: consumers deduce from it the induced ring and additive automorphisms of $R_w$, as in the construction of normal bases of lattices, the description of roots in terms of $q$-power maps, and the cocycle computations for subgroups of units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.algEquiv_apply_mem_Rw_iff (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    (σ : Kw ≃ₐ[ℚ_[q]] Kw) (x : Kw) : σ x ∈ Rw q Kw ↔ x ∈ Rw q Kw := by sorry
