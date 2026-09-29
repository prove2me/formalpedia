-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units
-- name    : ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/2d315c58-5bb3-515d-8eec-654654abf5c8
-- title:
--   Hilbert 90 for units along an injective restriction
-- statement:
--   Let $q$ be a prime, let $L$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}_q}$ (the algebraic closure `PadicAlgCl q`) which is finite-dimensional over $\mathbb{Q}_q$, and let $G$ be a finite group acting on $L$ by ring automorphisms (`MulSemiringAction`) faithfully, i.e. distinct elements of $G$ act differently on $L$. Assume further that $G$ fixes the image of $\mathbb{Q}_q$ in $L$ pointwise: $g \cdot x = x$ for every $g \in G$ and every $x$ in the image of the structure map $\mathbb{Q}_q \to L$. Assume given an action of $G$ on the unit group $L^{\times}$ by group automorphisms (`MulDistribMulAction`) compatible with the action on $L$, in the sense that the underlying element of $g \cdot u$ in $L$ equals $g \cdot u$ for all $g \in G$, $u \in L^{\times}$. Finally, let $\Gamma$ be a group and $f \colon \Gamma \to G$ an injective group homomorphism. The conclusion is that the degree-$1$ group cohomology object of the restriction along $f$ of the representation of $G$ on $L^{\times}$ (`Rep.ofMulDistribMulAction`) is a zero object.
--
--   This is Hilbert's Theorem 90, $H^1(\Gamma, L^{\times}) = 0$, for the action of $\Gamma$ on the units of a finite extension $L$ of $\mathbb{Q}_q$, stated along an arbitrary injective homomorphism $f \colon \Gamma \to G$ so that iterated restrictions of representations are covered. It is used as the vanishing input for the inflation–restriction arguments of the local theory, in particular in the construction and characterisation of local fundamental classes ([`ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass`](thm.html#ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass), [`ExtCitation.LocalLevel.isLocalFundamentalClass_of_pin`](thm.html#ExtCitation.LocalLevel.isLocalFundamentalClass_of_pin)) and in [`ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv`](thm.html#ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (Γ : Type) [Group Γ] (f : Γ →* G) (hf : Function.Injective f) :
    CategoryTheory.Limits.IsZero (groupCohomology (Rep.res f (Rep.ofMulDistribMulAction G (↥L)ˣ)) 1) := by sorry
