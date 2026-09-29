-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow
-- name    : ExtCitation.LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/18142e7e-e99e-5306-b977-65a66b0fdee2
-- title:
--   Ramification index, residue degree and ψ ≡ φ^f mod N
-- statement:
--   Fix a prime $q$ and write $\mathrm{Rw}\,q\,F$ for the valuation subring of an intermediate field $F$ of $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}_q}$ obtained by pulling back, along $F \to \overline{\mathbb{Q}_q}$, the valuation subring of the canonical valuation on $\overline{\mathbb{Q}_q}$. Let $L$ be such an intermediate field, finite over $\mathbb{Q}_q$, and let $G$ be a finite group acting on $L$ by ring automorphisms, faithfully, fixing every element of the image of $\mathbb{Q}_q$, together with a compatible action on $L^{\times}$ (the unit action agrees with the action on $L$ after coercion). Let $K \le L$ and $K' \le L$ be finite intermediate fields with $K$ the set of $G$-fixed elements of $L$ and $K'$ the set of $S$-fixed elements, for a subgroup $S \le G$, and let $N \trianglelefteq G$. Assume given $\varphi \in G$ with $\|\varphi \cdot x - x^{\#k}\| < 1$ for all $N$-fixed $x \in L$ with $\|x\| \le 1$, where $\#k = \mathrm{Nat.card}$ of the residue field of $\mathrm{Rw}\,q\,K$; a unit $\pi$ of $L$ fixed by all of $G$, with $\|\pi\| < 1$ and $\|y\| \le \|\pi\|$ for every $N$-fixed $y \in L$ with $\|y\| < 1$; an element $\psi \in S$ satisfying the corresponding congruence $\|\psi \cdot x - x^{\#k'}\| < 1$ for $(N \cap S)$-fixed integral $x$, with $\#k'$ the cardinality of the residue field of $\mathrm{Rw}\,q\,K'$; and a unit $\pi'$ of $L$ fixed by $S$, with $\|\pi'\| < 1$ and maximal in the same sense among $(N \cap S)$-fixed elements of norm $< 1$. The conclusion is the existence of natural numbers $e, f \ge 1$ with $e f = [G : S]$, $\|\pi\| = \|\pi'\|^{e}$, and $\psi \equiv \varphi^{f}$ in $G/N$.
--
--   This packages the ramification index and residue degree of the subextension $K'/K$ cut out by $S$, in the form needed to compare a Frobenius for the level $L^{N}$ with one for $L^{N \cap S}$: the two local invariants multiply to the index $[G:S]$, the uniformisers are related by the ramification index, and the Frobenius of the smaller base is a power of the Frobenius of the larger modulo $N$. It is used in the computation of the restriction of the local fundamental class, via [`ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv`](thm.html#ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv) and [`ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype`](thm.html#ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (φ : G) (hφ : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖)
    (ψ : S) (hψ : ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖(((ψ : G) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K'))‖ < 1)
    (π' : (↥L)ˣ) (hπ'S : ∀ s ∈ S, s • π' = π') (hπ'1 : ‖((π' : L) : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : L, (∀ n ∈ N ⊓ S, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π' : L) : PadicAlgCl q)‖) :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧ e * f = S.index ∧
      ‖((π : L) : PadicAlgCl q)‖ = ‖((π' : L) : PadicAlgCl q)‖ ^ e ∧
      (QuotientGroup.mk' N (ψ : G) = QuotientGroup.mk' N (φ ^ f)) := by sorry
