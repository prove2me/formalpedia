-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq
-- name    : ExtCitation.LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/4a9002d4-c3cf-5173-b171-166ee2cd18b3
-- title:
--   Fixed field of a finite group acting on a q-adic layer
-- statement:
--   Let $q$ be a prime, let $\overline{\mathbb{Q}}_q$ denote the fixed algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, and let $L$ be an intermediate field of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$ that is finite-dimensional over $\mathbb{Q}_q$. Let $G$ be a finite group acting on $L$ by ring automorphisms compatible with the multiplicative structure (`MulSemiringAction G L`), the action being faithful, and assume that every $g \in G$ fixes each element of the image of $\mathbb{Q}_q$ in $L$, i.e. $g \cdot \iota(x) = \iota(x)$ for all $g \in G$ and $x \in \mathbb{Q}_q$, where $\iota$ is the structure map $\mathbb{Q}_q \to L$. The conclusion asserts the existence of an intermediate field $K$ of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$, together with a witness that $K$ is finite-dimensional over $\mathbb{Q}_q$ (packaged as a second existential component), such that $K \le L$ as subfields of $\overline{\mathbb{Q}}_q$ and such that for every $x \in L$ the image of $x$ in $\overline{\mathbb{Q}}_q$ lies in $K$ if and only if $g \cdot x = x$ for all $g \in G$. Thus $K$ realises the fixed subfield $L^G$ as an intermediate field of the ambient extension $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$.
--
--   This is the existence of the fixed field $L^G$ of a finite group of $\mathbb{Q}_q$-automorphisms, presented in the form needed downstream: an intermediate field of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$, finite over $\mathbb{Q}_q$, contained in $L$, and characterised by the membership criterion. It is used as the input producing sub-layers inside a local extension, for instance in [`ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level`](thm.html#ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level), [`M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp`](thm.html#M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp) and [`NumberField.PlaceDecomp.exists_fundamentalClass_units_adicCompletion`](thm.html#NumberField.PlaceDecomp.exists_fundamentalClass_units_adicCompletion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), K ≤ L ∧
      ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x := by sorry
