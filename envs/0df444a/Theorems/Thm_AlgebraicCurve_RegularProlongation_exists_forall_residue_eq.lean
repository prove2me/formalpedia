-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/356fa718-7a00-510b-b328-e262e6471427
-- title:
--   Simultaneous residues at distinct regular prolongations
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue field $\mathrm{ResidueField}\,A$, let $F$ be a field with an $L$-algebra structure, let $\iota$ be a finite index type, and for each $i \in \iota$ let $\mathrm{Fb}\,i$ be a field that is an algebra over $\mathrm{ResidueField}\,A$. Suppose given for each $i$ a term $R\,i$ of `RegularProlongation A F (Fb i)`, that is: a valuation subring $(R\,i).\mathrm{integers}$ of $F$, a ring homomorphism $(R\,i).\mathrm{residue}$ from it to $\mathrm{Fb}\,i$, such that for $x \in L$ the image of $x$ in $F$ lies in $(R\,i).\mathrm{integers}$ exactly when $x \in A$; the residue map is surjective; its kernel is the maximal ideal of $(R\,i).\mathrm{integers}$; it carries the image of $a \in A$ to the image of the residue of $a$ under $\mathrm{ResidueField}\,A \to \mathrm{Fb}\,i$; and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in (R\,i).\mathrm{integers}$ and $(R\,i).\mathrm{residue}(c \cdot f) \neq 0$. Assume the map $i \mapsto (R\,i).\mathrm{integers}$ is injective. Then for every family $a$ with $a\,i \in \mathrm{Fb}\,i$ there is a single $z \in F$ lying in $(R\,i).\mathrm{integers}$ for all $i$ and satisfying $(R\,i).\mathrm{residue}(z) = a\,i$ for all $i$.
--
--   This is the weak-approximation statement that the joint residue map $\bigcap_i \mathcal{O}_i \to \prod_i \mathrm{Fb}\,i$ attached to finitely many distinct unramified prolongations of a valuation ring $A$ of $L$ to an extension field $F$ is surjective. It is used in the construction of monic generators with prescribed reductions over algebraically closed residue fields, and in producing finite integral spanning sets with surjective residue map in the reduction theory of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_residue_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Finite ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (a : ∀ i, Fb i) :
    ∃ z : F, ∀ i, ∃ h : z ∈ (R i).integers, (R i).residue ⟨z, h⟩ = a i := by sorry
