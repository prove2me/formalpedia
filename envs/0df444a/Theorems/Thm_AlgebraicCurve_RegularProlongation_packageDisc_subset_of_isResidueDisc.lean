-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_packageDisc_subset_of_isResidueDisc
-- name    : AlgebraicCurve.RegularProlongation.packageDisc_subset_of_isResidueDisc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a39d680e-d18c-5f76-85ac-20eb8474ec18
-- title:
--   A package disc is contained in a residue disc
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring subject to two conditions: for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$, and $A \neq L$ as a subset; $A$ is moreover assumed henselian local. Let $F$ be a field over $L$ which is a curve over $L$ (principal divisors of degree zero exist, all places have residue fields finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$, and let $\bar{F}$ be a field over the residue field of $A$ that is likewise a curve over it and essentially of finite type. Let $R$ be a regular prolongation of $A$ to $F$ with reduction $\bar{F}$, i.e. a valuation subring `R.integers` of $F$ together with a surjective reduction map onto $\bar{F}$ whose kernel is the maximal ideal, inducing the residue map of $A$ on $L$ and contracting every nonzero element of $F$ into the integers after scaling by $L$. Let $Q$ be a place of $\bar{F}$ over the residue field of $A$, and let $D$ be a set of places of $F/L$ and $z \in F$ such that $(D,z)$ is a residue disc for $(R,Q)$: $z$ is a disc coordinate (all $P \in D$ are rational, $z$ lies in each $P$ with $A$-valuation of $P.\mathrm{evalAt}(z)$ less than $1$; $z$ lies in the integers with reduction of $Q$-order $1$; each $c \in L$ of $A$-valuation $< 1$ is $P.\mathrm{evalAt}(z)$ for exactly one $P \in D$; $\mathrm{ord}_P(z - P.\mathrm{evalAt}(z)) = 1$ on $D$; and any nonzero $f$ with $\mathrm{ord}_P f = 0$ throughout $D$ has $A$-valuation of $P.\mathrm{evalAt}(f)$ constant on $D$ and equal to that of some $c \neq 0$), reduction is computed pointwise on $D$, and the degree clause holds: for $f$ in the integers with nonzero reduction, the sum over $D$ of $\mathrm{ord}_P f$ equals $Q.\mathrm{ord}$ of the reduction of $f$. Finally let $S' \subseteq F$ be a subring, $\varphi' : A[X] \to S'$ and $\chi_0' : S' \to \mathrm{ResidueField}(A)$ ring homomorphisms and $D'$ a set of places of $F/L$, satisfying the fourteen-clause smooth-point package: $A$ maps into $S'$; $\varphi'$ is formally smooth and formally unramified; $\varphi' \circ C$ is the structure map of $A$ and is carried by $\chi_0'$ to the residue map of $A$; $\chi_0'(\varphi' X) = 0$; for each $c$ in the maximal ideal of $A$ there is a unique $A$-section $\chi : S' \to A$ lifting $\chi_0'$, fixing $A$ and sending $\varphi' X$ to $c$; every element of $S'$ lies in `R.integers` with reduction in the valuation ring of $Q$ and $Q$-residue the image of its $\chi_0'$-value; the reduction of $\varphi' X$ has $Q$-order $1$; $D'$ consists exactly of the rational places $P$ at which every element of $S'$ is integral with $P.\mathrm{evalAt}$-value in $A$, that value having $A$-valuation $< 1$ precisely when $\chi_0'$ vanishes on it; each such $\chi$ arises from a unique $P \in D'$ via $P.\mathrm{evalAt}$; the valuation ring of each $P \in D'$ is the set of fractions $g/h$ with $g,h \in S'$ and $P.\mathrm{evalAt}(h) \neq 0$; any nonzero $f$ with $\mathrm{ord}_P f = 0$ throughout $D'$ becomes a unit of $S'$ after scaling by a nonzero element of $L$; and any $f$ in `R.integers` integral at all $P \in D'$ lies in $S'$. The conclusion is $D' \subseteq D$.
--
--   This is one half of the identification of a residue disc with the disc cut out by a smooth-point package: the companion statement gives $D \subseteq D'$ under the same hypotheses, so the two together yield $D = D'$. It is used in [`AlgebraicCurve.mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver`](thm.html#AlgebraicCurve.mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver), where membership in a residue disc is characterised by specialisation at a smooth point of the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_packageDisc_subset_of_isResidueDisc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.packageDisc_subset_of_isResidueDisc
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
    D' ⊆ D := by sorry
