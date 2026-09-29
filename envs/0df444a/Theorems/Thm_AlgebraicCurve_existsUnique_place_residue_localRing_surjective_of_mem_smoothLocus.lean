-- Prove2me | Theorems.Thm_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus
-- name    : AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/0f861486-eba1-5fbd-b48e-c7058585b910
-- title:
--   Smooth special point reduces to a unique rational place
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring which is a henselian local ring, is not all of $L$, and satisfies the rank-one condition that for all $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ there is $n$ with $b\mid a^{n}$. Let $F$ be a field extension of $L$ that is essentially of finite type and a curve over $L$ in the project's sense (every nonzero element has a degree-zero principal divisor, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank $1$ over $F$). Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism $\mathrm{toBase}\colon X\to\operatorname{Spec}A$, and $\varphi\colon F\simeq K(X)$ a ring isomorphism carrying $\mathrm{algebraMap}\,L\,F(a)$, for $a\in A$, to the image of $a$ under the structure map $A\to\Gamma(X,\mathcal O_X)\to K(X)$. Let $x\in X$ lie over the closed point of $\operatorname{Spec}A$, be closed in the specialisation order (every $y$ with $x\rightsquigarrow y$ equals $x$), and lie in the smooth locus of $\mathrm{toBase}$; let $\eta\neq x$ also lie over the closed point and satisfy $\eta\rightsquigarrow x$. Let $Fbar$ be a field extension of the residue field $\kappa$ of $A$ and $R$ a regular prolongation of $A$ to $F$ with values in $Fbar$: a valuation subring $\mathcal O_R\subseteq F$ together with a ring map $\mathrm{red}\colon\mathcal O_R\to Fbar$ which is surjective, has kernel the maximal ideal of $\mathcal O_R$, satisfies $\mathrm{algebraMap}\,L\,F(c)\in\mathcal O_R\iff c\in A$ and is compatible with $A\to\kappa\to Fbar$, and is such that every $f\neq 0$ in $F$ has a scaling $c\cdot f\in\mathcal O_R$ with nonzero reduction; assume the subring of $F$ underlying $\mathcal O_R$ is the image in $F$ under $\varphi^{-1}$ of the stalk $\mathcal O_{X,\eta}$ inside $K(X)$. Put $S\subseteq F$ for the corresponding image of the stalk $\mathcal O_{X,x}$. Then $S\subseteq\mathcal O_R$, and there is a place $Q$ of $Fbar$ over $\kappa$ (a valuation subring of $Fbar$ containing the image of $\kappa$, not equal to $Fbar$, and a principal ideal ring) such that: $\kappa$ surjects onto the residue field of $Q$; the reduction of every element of $S$ lies in $\mathcal O_Q$; every element of $\mathcal O_Q$ is the reduction of some element of $\mathcal O_R$ belonging to $S$; an element $f\in S$ is a unit of $S$ exactly when its reduction is nonzero of $Q$-order $0$; some $T\in S$ has reduction of $Q$-order $1$; and $Q$ is the only place of $Fbar$ over $\kappa$ whose valuation subring contains the reduction of $S$.
--
--   This is the statement that a smooth closed point of the special fibre of a model of a curve reduces to a rational place, with discrete valuation ring the image of $\mathcal O_{X,x}$, on the component of the special fibre determined by $\eta$. It feeds the construction of component charts for semistable models, being used in the identification of the smooth point rings and in the comparison of $\mathcal O_{X,x}$ with $\mathcal O_R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus
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
    (∀ f : ↥S, (f : F) ∈ R.integers) ∧
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ R.integers), f ∈ S ∧ R.residue ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ R.integers),
        IsUnit f ↔ Q.ord (R.residue ⟨(f : F), hR⟩) = 0 ∧ R.residue ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ R.integers), Q.ord (R.residue ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by sorry
