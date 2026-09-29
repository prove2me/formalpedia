-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_subset_packageDisc_of_isResidueDisc
-- name    : AlgebraicCurve.RegularProlongation.subset_packageDisc_of_isResidueDisc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/729cd490-bded-57a4-a0a4-b7771ab9f773
-- title:
--   A residue disc lies in any smooth-point package disc
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring which is a henselian local ring, is not all of $L$, and satisfies the rank-one condition that for all $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ there is an $n$ with $b\mid a^{n}$; write $\kappa$ for its residue field. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors of degree zero, residue fields of places finite over $L$, $\Omega_{F/L}$ free of rank one) and essentially of finite type over $L$, and let $\bar F$ be a curve over $\kappa$, essentially of finite type over $\kappa$. Let $R$ be a regular prolongation of $A$ to $F$ with reduction field $\bar F$: a valuation subring $\mathcal O_R\subseteq F$ meeting $L$ exactly in $A$, with a surjective ring map $f\mapsto\bar f$ onto $\bar F$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every $f\neq 0$ has an $L$-multiple lying in $\mathcal O_R$ with nonzero reduction. Let $Q$ be a place of $\bar F/\kappa$, let $D$ be a set of places of $F/L$ and $z\in F$, and assume $(D,z)$ is a residue disc for $R$ at $Q$, that is: $z$ is a disc coordinate, meaning every $P\in D$ is rational with $z\in\mathcal O_P$ and $|z(P)|<1$, and $z\in\mathcal O_R$ with $\operatorname{ord}_Q\bar z=1$, each $c\in L$ with $|c|<1$ equals $z(P)$ for exactly one $P\in D$, $z-z(P)$ has order $1$ at each $P\in D$, and any $f\neq 0$ with $\operatorname{ord}_P f=0$ throughout $D$ has $|f(P)|=|c|$ on $D$ for some $c\neq 0$; together with pointwise compatibility, namely that for rational $P\in D$ and $f\in\mathcal O_R$ regular on all of $D$ the value $f(P)$ lies in $A$ and its residue agrees in the residue field of $Q$ with the residue of $\bar f$; and the degree law, that for $f\in\mathcal O_R$ with $\bar f\neq 0$ and any divisor supported on $D$ agreeing there with $\operatorname{ord}_P f$, the sum of its coefficients is $\operatorname{ord}_Q\bar f$. Suppose further given a subring $S'\subseteq F$, ring maps $\varphi':A[X]\to S'$ and $\chi_0':S'\to\kappa$, and a set $D'$ of places of $F/L$ forming a smooth-point package at $(R,Q)$; the defining conditions, all summarised in the hypothesis, are: $A$ maps into $S'$; $\varphi'$ is formally smooth and formally unramified; $\varphi'\circ C$ is the structure map of $A$ into $F$ and $\chi_0'\circ\varphi'\circ C$ the residue map of $A$, while $\chi_0'(\varphi'X)=0$; for each $c\in A$ with residue $0$ there is exactly one $A$-section $\chi:S'\to A$ lifting $\chi_0'$ with $\chi(\varphi'X)=c$; every $f\in S'$ lies in $\mathcal O_R$, its reduction lies in the valuation ring of $Q$ and is read there as $\chi_0'(f)$; the reduction of $\varphi'X$ has $\operatorname{ord}_Q$ equal to $1$; $D'$ consists exactly of the rational places $P$ at which every $f\in S'$ is integral with $f(P)\in A$, and for which $|f(P)|<1$ if and only if $\chi_0'(f)=0$; each section $\chi$ as above corresponds to a unique $P\in D'$ with $f(P)=\chi(f)$ for all $f\in S'$; for $P\in D'$ the valuation ring $\mathcal O_P$ consists of the fractions $g/h$ with $g,h\in S'$ and $h(P)\neq 0$; any $f\neq 0$ with $\operatorname{ord}_P f=0$ throughout $D'$ becomes a unit of $S'$ after scaling by a nonzero element of $L$; and any $f\in\mathcal O_R$ lying in every $\mathcal O_P$ for $P\in D'$ lies in $S'$. The conclusion is $D\subseteq D'$.
--
--   This is the comparison between a residue class, given abstractly by a disc coordinate at a place $Q$ of the reduction, and the disc cut out by an étale chart at a smooth point lying over the same $Q$: the abstract residue disc is contained in the package's disc. It is the shared step in the identification of residue discs with formal fibres, used by [`AlgebraicCurve.exists_forall_specializes_of_isResidueDisc_of_reads_smooth`](thm.html#AlgebraicCurve.exists_forall_specializes_of_isResidueDisc_of_reads_smooth) and by [`AlgebraicCurve.mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver`](thm.html#AlgebraicCurve.mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver), and hence in the comparison of two packages attached to the same direction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_subset_packageDisc_of_isResidueDisc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.subset_packageDisc_of_isResidueDisc
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    [IsCurveOver (ResidueField ↥A) Fbar] [Algebra.EssFiniteType (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D : Set (Place L F)) (z : F) (hD : R.IsResidueDisc Q D z)
    (S' : Subring F) (φ' : Polynomial ↥A →+* ↥S') (χ₀' : ↥S' →+* ResidueField ↥A)
    (D' : Set (Place L F))
    (hpk' :
            (∀ a : ↥A, algebraMap L F (a : L) ∈ S') ∧
            (φ').FormallySmooth ∧ (φ').FormallyUnramified ∧
            (∀ a : ↥A, ((φ' (Polynomial.C a) : ↥(S')) : F) = algebraMap L F (a : L)) ∧
            (∀ a : ↥A, χ₀' (φ' (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀' (φ' Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S') →+* ↥A, (∀ a : ↥A, χ (φ' (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S'), IsLocalRing.residue ↥A (χ f) = χ₀' f) ∧ χ (φ' Polynomial.X) = c) ∧
            (∀ f : ↥(S'), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀' f)) ∧
            (∃ hR : ((φ' Polynomial.X : ↥(S')) : F) ∈ R.integers,
              Q.ord (R.residue ⟨((φ' Polynomial.X : ↥(S')) : F), hR⟩) = 1) ∧
            (∀ P, P ∈ D' ↔ (P.IsRational ∧ (∀ f : ↥(S'), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
              (∀ f : ↥(S'), A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀' f = 0))) ∧
            (∀ χ : ↥(S') →+* ↥A, (∀ a : ↥A, χ (φ' (Polynomial.C a)) = a) →
              (∀ f : ↥(S'), IsLocalRing.residue ↥A (χ f) = χ₀' f) →
              ∃! P, P ∈ D' ∧ ∀ f : ↥(S'), P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
            (∀ P ∈ D', ∀ f : F, f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S'), P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
            (∀ f : F, f ≠ 0 → (∀ P ∈ D', P.ord f = 0) →
              ∃ (c : L) (u : (↥(S'))ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥(S')) : F)) ∧
            (∀ f : F, f ∈ R.integers → (∀ P ∈ D', f ∈ P.toValuationSubring) → f ∈ S')) :
    D ⊆ D' := by sorry
