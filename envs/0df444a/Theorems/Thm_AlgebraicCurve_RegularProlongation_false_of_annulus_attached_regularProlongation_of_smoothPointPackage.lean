-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_false_of_annulus_attached_regularProlongation_of_smoothPointPackage
-- name    : AlgebraicCurve.RegularProlongation.false_of_annulus_attached_regularProlongation_of_smoothPointPackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/b6f71a4a-efaa-5d21-a84c-533edfab9762
-- title:
--   Incompatibility of a reciprocal annulus pair at a smooth point
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring with residue field $\kappa$, $F$ a field extension of $L$ and $\bar F$ a field extension of $\kappa$; let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$ (a valuation subring $R.\mathrm{integers}$ of $F$ whose contraction to $L$ is $A$, together with a surjective residue map to $\bar F$ whose kernel is the maximal ideal and which extends the residue map of $A$, and such that every nonzero element of $F$ has an $L$-multiple that is integral with nonzero residue), and let $Q$ be a place of $\bar F$ over $\kappa$, i.e. a proper valuation subring containing the image of $\kappa$ and which is a principal ideal ring. Assume given the following data at $(R,Q)$: a subring $S\subseteq F$ containing the image of $A$; a ring map $\varphi:A[X]\to S$ that is formally smooth and formally unramified and carries a constant $a$ to the image of $a$; a character $\chi_0:S\to\kappa$ with $\chi_0(\varphi(C\,a))$ the residue of $a$ and $\chi_0(\varphi(X))=0$; the chart property that for each $c\in A$ of residue zero there is exactly one ring map $\chi:S\to A$ fixing the constants, lifting $\chi_0$ and sending $\varphi(X)$ to $c$; the containment $S\subseteq R.\mathrm{integers}$ with every $R$-residue of an element $f$ of $S$ lying in $Q$ and reducing to the image of $\chi_0(f)$ in the residue field of $Q$, and $\mathrm{ord}_Q$ of the $R$-residue of $\varphi(X)$ equal to $1$. Assume further a set $D$ of places $P$ of $F$ over $L$ such that every $P\in D$ is rational (the structure map $L\to$ residue field of $P$ is surjective), $S$ lies in the valuation ring of $P$ with all evaluations $P.\mathrm{evalAt}(f)$ in $A$, and $|P.\mathrm{evalAt}(f)|<1$ holds exactly when $\chi_0(f)=0$; every $A$-section $\chi$ of $S$ lifting $\chi_0$ is realised by a unique $P\in D$ with $P.\mathrm{evalAt}(f)=\chi(f)$ for all $f$; for $P\in D$ the valuation ring of $P$ consists of the quotients $g/h$ with $g,h\in S$ and $P.\mathrm{evalAt}(h)\neq 0$; every nonzero $f\in F$ with $\mathrm{ord}_P f=0$ for all $P\in D$ becomes, after multiplication by a nonzero scalar from $L$, a unit of $S$; and every $f\in R.\mathrm{integers}$ lying in all the valuation rings of $D$ lies in $S$. Let finally $An'$ and $An$ be annuli for $A$ in $F$ with the same domain and the same modulus $\mu$, with $\mu\neq 0$ in $L$ and $An'.\mathrm{param}\cdot An.\mathrm{param}$ equal to the image of $\mu$; assume $An'.\mathrm{param}$ lies in $R.\mathrm{integers}$ with $\mathrm{ord}_Q$ of its residue equal to $1$ and the slope law that for every $g\in R.\mathrm{integers}$ with nonzero $R$-residue and $\mathrm{ord}_P g=0$ for all $P$ in the domain, the element $P.\mathrm{evalAt}(g)\cdot P.\mathrm{evalAt}(An'.\mathrm{param})^{-\mathrm{ord}_Q(\bar g)}$ lies in $A$ and is a unit there for all such $P$; assume the same attachment data for $An.\mathrm{param}$ relative to a second regular prolongation $R_x$ of $A$ to $F$ with values in a field $\bar F'$ over $\kappa$ and a place $b_x$ of $\bar F'$ over $\kappa$; assume the domain of $An'$ contains two places at which $An'.\mathrm{param}$ has distinct values under the valuation of $A$; and assume there is $f\in S$ with $\chi_0(f)=0$, $f\neq 0$, both $f$ and $f^{-1}$ in $R_x.\mathrm{integers}$, and $\mathrm{ord}_P f=0$ for every $P$ in the domain of $An'$. Then these hypotheses are contradictory: the conclusion is `False`.
--
--   The statement records that an annulus attached at a smooth point of the reduction cannot have its opposite end attached to a further regular prolongation in which a function vanishing at that smooth point is a unit; it is the chart-free form of the non-Archimedean rigidity used when comparing the two slope laws along a reciprocal pair of annuli. It is invoked by the three full-level modular curve statements [`ModularCurve.FullLevel.not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel`](thm.html#ModularCurve.FullLevel.not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel), and its variants for the primes $3$ and $2$, to rule out configurations in the analysis of the ends of Igusa-type components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_false_of_annulus_attached_regularProlongation_of_smoothPointPackage.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.false_of_annulus_attached_regularProlongation_of_smoothPointPackage
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
    (hloc' : ∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S)

    (An' An : Annulus A F)
    (hAn : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ (An.modulus : L) ≠ 0 ∧
      An'.param * An.param = algebraMap L F (An.modulus : L))
    (hnear : ∃ hz : An'.param ∈ R.integers, Q.ord (R.residue ⟨An'.param, hz⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord g = 0) →
        ∀ P ∈ An'.dom, ∃ h : P.evalAt g * (P.evalAt An'.param) ^ (-(Q.ord (R.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    {Fbar' : Type*} [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
    (Rx : RegularProlongation A F Fbar') (bx : Place (ResidueField ↥A) Fbar')
    (hfar : ∃ hz : An.param ∈ Rx.integers, bx.ord (Rx.residue ⟨An.param, hz⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ Rx.integers), Rx.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) →
        ∀ P ∈ An.dom, ∃ h : P.evalAt g * (P.evalAt An.param) ^ (-(bx.ord (Rx.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (hdom : ∃ P₁ ∈ An'.dom, ∃ P₂ ∈ An'.dom, A.valuation (P₁.evalAt An'.param) ≠ A.valuation (P₂.evalAt An'.param))

    (hsep : ∃ f : ↥S, χ₀ f = 0 ∧ (f : F) ≠ 0 ∧ (f : F) ∈ Rx.integers ∧ (f : F)⁻¹ ∈ Rx.integers ∧
      ∀ P ∈ An'.dom, P.ord (f : F) = 0) :
    False := by sorry
