-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver
-- name    : AlgebraicCurve.mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/4d579bff-e586-556c-9b9b-546011564a74
-- title:
--   Residue discs are the formal fibres at smooth special points
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring such that for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is an $n$ with $b \mid a^{n}$, with $A \neq L$ as a subset and with $A$ henselian local. Let $F/L$ be an extension which is a curve over $L$ in the project's sense (principal divisors of degree zero exist for every nonzero function, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$. Let $X$ be an integral scheme and $toBase : X \to \operatorname{Spec} A$ proper, flat and locally of finite presentation, all of whose stalks are integrally closed, and let $\varphi$ be a ring isomorphism $F \cong K(X)$ compatible with the maps of $A$ into both sides. Let $x \in X$ lie over the closed point of $A$, be closed (every $y$ to which $x$ specialises equals $x$) and lie in the smooth locus of $toBase$, and let $\eta \neq x$ lie over the closed point of $A$ and specialise to $x$. Let $\bar F$ be a field over the residue field $\kappa$ of $A$ which is likewise a curve over $\kappa$ and essentially of finite type over it, and let $R$ be a regular prolongation of $A$ to $F$ with reductions in $\bar F$: a valuation subring $R.\mathrm{integers}$ of $F$ whose intersection with $L$ is exactly $A$, together with a surjective ring map $R.\mathrm{residue}$ onto $\bar F$ with kernel the maximal ideal, compatible with reduction on $A$, and such that every nonzero $f \in F$ has an $L$-multiple in $R.\mathrm{integers}$ with nonzero reduction; assume $R.\mathrm{integers}$ coincides, as a subring of $F$, with the image $\mathrm{localRing}\,X\,\varphi\,\eta$ of the stalk at $\eta$ in $F$. Let $Q$ be a place of $\bar F/\kappa$ (a valuation subring containing $\kappa$, not all of $\bar F$, with principal ideals) such that every $f \in R.\mathrm{integers}$ lying in the image of the stalk at $x$ reduces into $Q$. Finally let $D$ be a set of places of $F/L$ and $z \in F$ with $R.\mathrm{IsResidueDisc}\,Q\,D\,z$, that is: $z$ lies in $R.\mathrm{integers}$ with $\operatorname{ord}_Q$ of its reduction equal to $1$, every $P \in D$ is rational with $z \in \mathcal O_P$ and $|z(P)| < 1$, every $c \in L$ with $|c| < 1$ is the value $z(P)$ for exactly one $P \in D$, $z - z(P)$ has order $1$ at each $P \in D$, any nonzero $f$ with order $0$ along all of $D$ has constant nonzero absolute value of its values on $D$; pointwise compatibility (for rational $P \in D$ and $f \in R.\mathrm{integers}$ regular on all of $D$, the value $f(P)$ lies in $A$ and its reduction agrees with the residue of $\bar f$ at $Q$); and the degree law $\sum_{P \in D} \operatorname{ord}_P f = \operatorname{ord}_Q \bar f$ for $f \in R.\mathrm{integers}$ with nonzero reduction. The conclusion is that for every place $P$ of $F/L$, $P \in D$ if and only if every $f$ in the image of the stalk $\mathcal O_{X,x}$ in $F$ lies in the valuation ring of $P$, has value $P.\mathrm{evalAt}\,f \in A$, and this value is a unit of $A$ exactly when $f$ is invertible inside that image subring.
--
--   The statement identifies an abstract residue disc $(D,z)$ attached to a regular prolongation $R$ and a place $Q$ of the reduction with the formal fibre of the model $X \to \operatorname{Spec} A$ at the smooth closed special point $x$: membership in $D$ is characterised by the condition that $\mathcal O_{X,x} \to F$ carries the stalk into $\mathcal O_P$, values into $A$, and non-units to non-units. It is used in the construction of a smooth centre for a residue disc, which feeds the geometric input of the analysis of curves over henselian valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.mem_iff_specializes_of_isResidueDisc_of_mem_smoothLocus_of_isCurveOver
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    [IsCurveOver (ResidueField ↥A) Fbar] [Algebra.EssFiniteType (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (Q : Place (ResidueField ↥A) Fbar)
    (hQ : ∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring)

    (D : Set (Place L F)) (z : F) (hD : R.IsResidueDisc Q D z) :
    ∀ P : Place L F, P ∈ D ↔
      ∀ f : F, f ∈ SemistableModel.localRing X φ x →
        f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1) := by sorry
