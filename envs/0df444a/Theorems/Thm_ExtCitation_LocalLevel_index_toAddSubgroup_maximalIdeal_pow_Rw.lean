-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw
-- name    : ExtCitation.LocalLevel.index_toAddSubgroup_maximalIdeal_pow_Rw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/6c7841dd-8e8d-5b2d-8424-0b60fb554ddd
-- title:
--   Index of mathfrak m_wⁿ in R_w equals (#κ_w)ⁿ
-- statement:
--   Let $q$ be a prime number and let $K_w$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ (the algebraic closure `PadicAlgCl q`) which is finite-dimensional over $\mathbb{Q}_q$; let $n$ be a natural number. Write $R_w =$ `Rw q Kw` for the valuation subring of $K_w$ obtained by pulling back, along the structure map $K_w \to \overline{\mathbb{Q}}_q$, the valuation subring attached to the $\mathbb{R}_{\ge 0}$-valued valuation on $\overline{\mathbb{Q}}_q$ (that is, the ring of elements of $K_w$ that are integral for the canonical extension of the $q$-adic absolute value). Let $\mathfrak m_w$ denote the maximal ideal of the local ring $R_w$. The assertion is the conjunction of two statements about the ideal $\mathfrak m_w^n$ regarded as an additive subgroup of $R_w$: first, that this additive subgroup has finite index, and second, that its index equals $(\#\kappa_w)^n$, where $\#\kappa_w$ is the cardinality (in the sense of `Nat.card`) of the residue field of $R_w$.
--
--   This is the standard index computation for powers of the maximal ideal in the ring of integers of a finite extension of $\mathbb{Q}_q$, with the $\mathbb{R}_{\ge 0}$-valued valuation model of that ring used throughout the local-level computations. It feeds the finite-index hypotheses of the dévissage lemma [`ExtCitation.LocalLevel.finiteIndex_toAddSubgroup_span_pow_Rw`](thm.html#ExtCitation.LocalLevel.finiteIndex_toAddSubgroup_span_pow_Rw) and the rank computation [`ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_Kw_of_basis`](thm.html#ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_Kw_of_basis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.index_toAddSubgroup_maximalIdeal_pow_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (n : ℕ) :
    (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.FiniteIndex ∧
      (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.index
        = Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ n := by sorry
