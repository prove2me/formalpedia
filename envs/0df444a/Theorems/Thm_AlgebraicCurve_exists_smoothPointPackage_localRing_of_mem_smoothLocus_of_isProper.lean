-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper
-- name    : AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/c35e9514-543b-5fdf-8ad7-70000c3c48c2
-- title:
--   Residue-disc package at a smooth closed point of a model
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring which is henselian local, which is not all of $L$, and which satisfies the rank-one condition that for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ some power $a^n$ is divisible by $b$. Let $F$ be a field extension of $L$ which is essentially of finite type and is a curve over $L$ in the project's sense (every nonzero element of $F$ has a degree-zero principal divisor on the places of $F/L$, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$). Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism $\mathrm{toBase} \colon X \to \operatorname{Spec} A$, and $\varphi \colon F \cong K(X)$ a ring isomorphism compatible with the two maps from $A$. Let $x \in X$ lie over the closed point of $A$, specialise only to itself, and lie in the smooth locus of $\mathrm{toBase}$, and let $\eta \neq x$ be a further point over the closed point specialising to $x$. Let $\overline{F}$ be an extension of the residue field of $A$ and $R$ a regular prolongation of $A$ to $F$ with reduction to $\overline{F}$ (a valuation subring $R.\mathrm{integers} \subseteq F$ inducing $A$ on $L$, together with a surjective residue map to $\overline{F}$ with kernel the maximal ideal, compatible with $A \to \overline{F}$, and such that every nonzero $f \in F$ has an $L$-multiple with nonzero residue), and assume $R.\mathrm{integers}$, viewed as a subring of $F$, is the image of the stalk $\mathcal{O}_{X,\eta}$ in $F$. Put $S \subseteq F$ for the image of $\mathcal{O}_{X,x}$ in $F$ under $\varphi^{-1}$. The assertion is the existence of a place $Q$ of $\overline{F}$ over the residue field of $A$, a ring homomorphism $\varphi_T \colon A[T] \to S$, a ring homomorphism $\chi_0 \colon S \to \operatorname{ResidueField} A$, and a set $D$ of places of $F/L$, such that: $Q$ is rational (the residue field of $A$ surjects onto the residue field of $Q$); $Q$ is the unique place $Q'$ of $\overline{F}$ with the property that every $f \in S$ lies in $R.\mathrm{integers}$ with $R$-residue in the valuation subring of $Q'$; $S$ contains the image of $A$; $\varphi_T$ is formally smooth and formally unramified; $\varphi_T(C a)$ is the image of $a$ in $F$ for $a \in A$, $\chi_0(\varphi_T(C a))$ is the residue of $a$, and $\chi_0(\varphi_T(T)) = 0$; for every $c$ in the maximal ideal of $A$ there is exactly one ring homomorphism $\chi \colon S \to A$ which is the identity on the coefficients, reduces to $\chi_0$, and sends $\varphi_T(T)$ to $c$; every $f \in S$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and its residue there is the image of $\chi_0(f)$ in the residue field of $Q$; the $R$-residue of $\varphi_T(T)$ has $Q$-order $1$; $D$ consists exactly of the rational places $P$ of $F/L$ such that every $f \in S$ lies in the valuation subring of $P$ with $P$-value $\mathrm{evalAt}_P(f) \in A$, and such that $\mathrm{evalAt}_P(f)$ has $A$-valuation $< 1$ precisely when $\chi_0(f) = 0$; every ring homomorphism $\chi \colon S \to A$ which is the identity on coefficients and reduces to $\chi_0$ comes from a unique $P \in D$ via $\mathrm{evalAt}_P = \chi$; for $P \in D$ the valuation subring of $P$ consists of the quotients $g/h$ with $g, h \in S$ and $\mathrm{evalAt}_P(h) \neq 0$; any nonzero $f \in F$ with $\mathrm{ord}_P f = 0$ for all $P \in D$ becomes a unit of $S$ after multiplication by a nonzero element of $L$; and any $f \in R.\mathrm{integers}$ lying in the valuation subring of every $P \in D$ already lies in $S$.
--
--   This is the statement that the formal fibre of a smooth closed point $x$ of a proper flat model over a henselian rank-one valuation ring is a residue disc: the local ring $\mathcal{O}_{X,x}$, read inside the function field, admits an étale coordinate over $A$, and its $A$-sections correspond bijectively to the places of $F/L$ reducing to $x$, with $\mathcal{O}_P$ recovered as a localisation of $S$ and a unit principle and locality statement off $D$. It supplies the 'model to covering' half of the dictionary between semistable models and chart data, and is used in the specialisation and membership criteria for residue discs and in the descent of semistable models for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_smoothPointPackage_localRing_of_mem_smoothLocus_of_isProper
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    ∃ (Q : Place (ResidueField ↥A) Fbar) (φT : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
      (D : Set (Place L F)),
      Q.IsRational ∧

      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) ∧
      (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
      φT.FormallySmooth ∧ φT.FormallyUnramified ∧
      (∀ a : ↥A, ((φT (Polynomial.C a) : ↥S) : F) = algebraMap L F (a : L)) ∧
      (∀ a : ↥A, χ₀ (φT (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
      χ₀ (φT Polynomial.X) = 0 ∧
      (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
        ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) ∧
          (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φT Polynomial.X) = c) ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
          algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
      (∃ hR : ((φT Polynomial.X : ↥S) : F) ∈ R.integers,
        Q.ord (R.residue ⟨((φT Polynomial.X : ↥S) : F), hR⟩) = 1) ∧
      (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
      (∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φT (Polynomial.C a)) = a) →
        (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
        ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
      (∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔
        ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
        ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F)) ∧
      (∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) := by sorry
