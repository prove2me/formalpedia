-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable
-- name    : ExtCitation.LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/a579dde5-cef0-54a9-847b-afbd5f660974
-- title:
--   Local second inequality for H²(G,L^×), G solvable
-- statement:
--   Fix a prime $q$ and let $L$ be an intermediate field of the extension $\mathbb{Q}_q \subset \overline{\mathbb{Q}}_q$ (the algebraic closure `PadicAlgCl q`) which is finite-dimensional over $\mathbb{Q}_q$. Let $G$ be a finite group, assumed solvable, acting on $L$ by ring automorphisms (a `MulSemiringAction`), the action being faithful and fixing every element of the image of $\mathbb{Q}_q$ under the structure map $\mathbb{Q}_q \to L$, so that $G$ acts by $\mathbb{Q}_q$-algebra automorphisms; let a multiplicative distributive action of $G$ on the unit group $L^\times$ be given, compatible with the action on $L$ in the sense that the underlying element of $g \cdot u$ in $L$ equals $g \cdot u$ for all $g \in G$ and $u \in L^\times$. The conclusion concerns the second group cohomology of the $\mathbb{Z}$-linear representation of $G$ on (the additive copy of) $L^\times$ attached to this action, `Rep.ofMulDistribMulAction G (↥L)ˣ`: the group $H^2(G, L^\times)$ is finite and its cardinality is at most the cardinality of $G$.
--
--   This is the second inequality of local class field theory, $\#H^2(G,L^\times) \le \#G = [L:L^G]$, for a finite solvable group of $\mathbb{Q}_q$-automorphisms of a finite extension $L$ of $\mathbb{Q}_q$; solvability is imposed as a hypothesis rather than deduced from the ramification filtration. It feeds the local computations of the Brauer group and of the fundamental class used downstream, for instance in [`ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass`](thm.html#ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass) and [`ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level`](thm.html#ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation.LocalLevel IsLocalRing groupCohomology

theorem ExtCitation.LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] (hsolv : Group.IsSolvable G) [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) :
    Finite (groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) ∧
      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) ≤ Nat.card G := by sorry
