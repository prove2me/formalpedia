-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_forall_mem_and_isUnit_iff_of_mem_packageDisc
-- name    : AlgebraicCurve.RegularProlongation.forall_mem_and_isUnit_iff_of_mem_packageDisc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/4aefe5e5-cd00-57b1-9167-921163ceabdb
-- title:
--   Places of a package disc read units of S
-- statement:
--   Let $L$ be an algebraically closed field, $A$ a valuation subring of $L$ with residue field $\kappa$, $F$ a field extension of $L$, and $\bar F$ a field extension of $\kappa$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$, i.e. a valuation subring `R.integers` of $F$ together with a surjective ring homomorphism `R.residue` to $\bar F$ whose kernel is the maximal ideal, which pulls back to $A$ along $L \to F$, is compatible with $A \to \kappa \to \bar F$ on constants, and is such that every nonzero $f \in F$ has a scalar multiple $cf$ ($c \in L$) that is integral with nonzero residue; let $Q$ be a place of $\bar F$ over $\kappa$, that is a proper valuation subring of $\bar F$ containing the image of $\kappa$ and which is a principal ideal ring. Let $S$ be a subring of $F$, $\varphi_T : A[X] \to S$ and $\chi_0 : S \to \kappa$ ring homomorphisms, and $D_p$ a set of places of $F$ over $L$. The hypothesis `hpk` is a conjunction of fourteen clauses, summarised here: $A$ maps into $S$; $\varphi_T$ is formally smooth and formally unramified; $\varphi_T(C\,a)$ is the image of $a$ in $F$ and $\chi_0(\varphi_T(C\,a))$ is the residue of $a$, while $\chi_0(\varphi_T X) = 0$; for every $c \in A$ of zero residue there is a unique ring homomorphism $\chi : S \to A$ splitting $\varphi_T \circ C$, lifting $\chi_0$ and sending $\varphi_T X$ to $c$; every $f \in S$ is $R$-integral with $R$-residue in $Q$, whose $Q$-residue is the image of $\chi_0 f$, and $\varphi_T X$ has $R$-residue of $Q$-order $1$; a place $P$ lies in $D_p$ exactly when $P$ is rational (the structure map $L \to$ its residue field is surjective), $S$ lies in the valuation subring of $P$ with all values $P.\mathrm{evalAt}\,f$ in $A$, and $A$-valuation of $P.\mathrm{evalAt}\,f$ is $<1$ iff $\chi_0 f = 0$; sections $\chi$ as above correspond bijectively to points of $D_p$ via their value maps; for $P \in D_p$ the valuation subring of $P$ consists of fractions $g/h$ with $g, h \in S$ and $h(P) \neq 0$; a nonzero $f \in F$ with $P$-order $0$ at all $P \in D_p$ becomes, after multiplication by a nonzero scalar from $L$, a unit of $S$; and an $R$-integral $f$ lying in all $P \in D_p$ belongs to $S$. The conclusion: for each place $P \in D_p$ and each $f \in S$, $f$ lies in the valuation subring of $P$, its value $P.\mathrm{evalAt}\,f$ (the element of $L$ whose image in the residue field of $P$ is the residue of $f$) lies in $A$, and that element is a unit of $A$ if and only if there is $g \in S$ with $fg = 1$.
--
--   This is the bookkeeping step that converts membership of a place in a smooth-point package disc $D_p$ into the local-homomorphism form used by model statements: every element of the package ring $S$ is regular at $P$, takes its value in $A$, and is a unit of $A$ there precisely when it is already invertible in $S$. It is used in the proof of [`AlgebraicCurve.exists_forall_specializes_of_isResidueDisc_of_reads_smooth`](thm.html#AlgebraicCurve.exists_forall_specializes_of_isResidueDisc_of_reads_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_forall_mem_and_isUnit_iff_of_mem_packageDisc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.forall_mem_and_isUnit_iff_of_mem_packageDisc
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (S : Subring F) (φT : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A) (Dp : Set (Place L F))
    (hpk :
            (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
            (φT).FormallySmooth ∧ (φT).FormallyUnramified ∧
            (∀ a : ↥A, ((φT (Polynomial.C a) : ↥(S)) : F) = algebraMap L F (a : L)) ∧
            (∀ a : ↥A, χ₀ (φT (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φT Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φT Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φT Polynomial.X : ↥(S)) : F) ∈ R.integers,
              Q.ord (R.residue ⟨((φT Polynomial.X : ↥(S)) : F), hR⟩) = 1) ∧
            (∀ P, P ∈ Dp ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ Dp ∧ ∀ f : ↥(S), P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
            (∀ P ∈ Dp, ∀ f : F, f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
            (∀ f : F, f ≠ 0 → (∀ P ∈ Dp, P.ord f = 0) →
              ∃ (c : L) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥(S)) : F)) ∧
            (∀ f : F, f ∈ R.integers → (∀ P ∈ Dp, f ∈ P.toValuationSubring) → f ∈ S))
    (P : Place L F) (hP : P ∈ Dp) :
    ∀ f : F, f ∈ S → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
      (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ S, f * g = 1) := by sorry
