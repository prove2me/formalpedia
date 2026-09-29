-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_isResidueDisc_of_etaleChart_of_sections
-- name    : AlgebraicCurve.RegularProlongation.isResidueDisc_of_etaleChart_of_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/5c0e93e1-e704-57c9-bc07-88c44aa6d0d0
-- title:
--   Étale chart with sections gives a residue disc
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, $F/L$ a field extension and $\bar F$ a field extension of the residue field $\kappa$ of $A$; let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$ (a valuation subring $R.\mathrm{integers}$ of $F$ together with a surjective ring map $R.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, cutting out $A$ on $L$, compatible with $A\to\kappa$, and such that every nonzero $f\in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero reduction), and let $Q$ be a place of $\bar F$ over $\kappa$ (a proper valuation subring of $\bar F$ containing the image of $\kappa$ and a principal ideal ring). Assume given a subring $S\subseteq F$ containing the image of $A$; a ring map $\varphi:A[X]\to S$ which is formally smooth and formally unramified and satisfies $\varphi(C\,a)=a$ in $F$ for $a\in A$; and a ring map $\chi_0:S\to\kappa$ with $\chi_0(\varphi(C\,a))=\bar a$ and $\chi_0(t)=0$, where $t:=\varphi(X)$. Assume further: (hchart) for each $c\in A$ with $\bar c=0$ there is exactly one ring map $\chi:S\to A$ with $\chi\circ\varphi\circ C=\mathrm{id}_A$, $\overline{\chi(f)}=\chi_0(f)$ for all $f$, and $\chi(t)=c$; (hSR) $S\subseteq R.\mathrm{integers}$; (hres) for every $f\in S$ the reduction $R.\mathrm{residue}(f)$ lies in $Q$'s valuation subring and its $Q$-residue is the image of $\chi_0(f)$ in the residue field of $Q$; (hordQ) $\mathrm{ord}_Q(R.\mathrm{residue}(t))=1$. Let $D$ be a set of places of $F/L$ such that (hD) every $P\in D$ is rational (i.e. $L\to$ residue field of $P$ is surjective), every $f\in S$ lies in $P$'s valuation subring with $P.\mathrm{evalAt}(f)\in A$, and $A$'s valuation of $P.\mathrm{evalAt}(f)$ is $<1$ exactly when $\chi_0(f)=0$; (hsec) every ring map $\chi:S\to A$ with $\chi\circ\varphi\circ C=\mathrm{id}_A$ and $\overline{\chi(\cdot)}=\chi_0$ is the evaluation map $f\mapsto P.\mathrm{evalAt}(f)$ of exactly one $P\in D$; (hval) for $P\in D$, $f$ lies in $P$'s valuation subring iff $f\,h=g$ for some $g,h\in S$ with $P.\mathrm{evalAt}(h)\neq 0$; (hloc) every nonzero $f\in F$ with $\mathrm{ord}_P f=0$ for all $P\in D$ becomes a unit of $S$ after multiplication by a nonzero element of $L$; (hloc') every $f\in R.\mathrm{integers}$ lying in the valuation subring of every $P\in D$ belongs to $S$. The conclusion is that $t$ is a residue disc coordinate for $R$, $Q$ and $D$ in the strong sense of `IsResidueDisc`: $t$ is a disc coordinate (all $P\in D$ are rational with $t\in\mathcal O_P$ and $A$-valuation of $P.\mathrm{evalAt}(t)$ less than $1$; $t\in R.\mathrm{integers}$ with $\mathrm{ord}_Q$ of its reduction equal to $1$; for each $c\in L$ of $A$-valuation $<1$ there is exactly one $P\in D$ with $P.\mathrm{evalAt}(t)=c$; $\mathrm{ord}_P(t-P.\mathrm{evalAt}(t))=1$ for $P\in D$; and any nonzero $f$ with $\mathrm{ord}_P f=0$ throughout $D$ has constant $A$-valuation of $P.\mathrm{evalAt}(f)$, equal to that of some nonzero $c\in L$), the pair $(Q,D)$ is pointwise compatible (for $P\in D$ rational and $f\in R.\mathrm{integers}$ regular at every place of $D$, the reduction of $f$ lies in $Q$'s valuation subring, $P.\mathrm{evalAt}(f)\in A$, and the two residues agree in the residue field of $Q$), and the degree condition holds (for $f\in R.\mathrm{integers}$ with nonzero reduction, any divisor supported in $D$ whose multiplicity at each $P\in D$ is $\mathrm{ord}_P f$ has total degree $\mathrm{ord}_Q(R.\mathrm{residue}(f))$).
--
--   This is the formal-fibre statement that a smooth point of a model, presented by an étale chart to the affine line together with the bijection between $A$-sections of the chart and the rational points specialising to that point, gives a residue disc of the component whose Gauss prolongation is $R$, with the point read off as the place $Q$. It feeds the packaging lemmas relating residue discs to their associated collections of places, and the construction of semistable coverings of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_isResidueDisc_of_etaleChart_of_sections.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.isResidueDisc_of_etaleChart_of_sections
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)

    (S : Subring F) (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
    (φ : Polynomial ↥A →+* ↥S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified)
    (hφC : ∀ a : ↥A, ((φ (Polynomial.C a) : ↥S) : F) = algebraMap L F (a : L))
    (χ₀ : ↥S →+* ResidueField ↥A) (hχ₀C : ∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a)
    (hχ₀t : χ₀ (φ Polynomial.X) = 0)

    (hchart : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
      ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c)

    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)
    (hres : ∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f))
    (hordQ : Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : F), hSR (φ Polynomial.X)⟩) = 1)

    (D : Set (Place L F))
    (hD : ∀ P ∈ D, P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))

    (hsec : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
      (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L))

    (hval : ∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F))

    (hloc : ∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
      ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F))
    (hloc' : ∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) :
    R.IsResidueDisc Q D ((φ Polynomial.X : ↥S) : F) := by sorry
