-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_forall_specializes_of_isResidueDisc_of_reads_smooth
-- name    : AlgebraicCurve.exists_forall_specializes_of_isResidueDisc_of_reads_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2a0330e6-e350-59c3-9341-6fb4d29e330b
-- title:
--   Residue discs lie in the formal fibre of a smooth centre
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring that is henselian local, is not all of $L$, and satisfies: for all $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ there is $n$ with $b\mid a^{n}$. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors exist, all places have residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type over $L$. Let $X$ be a scheme with a morphism $\mathrm{toBase}\colon X\to\operatorname{Spec}A$, with $X$ integral and $\mathrm{toBase}$ proper, flat and locally of finite presentation, all stalks of $X$ integrally closed, together with a ring isomorphism $\varphi\colon F\xrightarrow{\sim}K(X)$ compatible with the two maps from $A$ (the one through $L\subseteq F$ and `SemistableModel.baseToFunctionField`). Let $\eta\in X$ lie over the closed point of $A$ and be non-closed. Let $\bar F$ be a field over the residue field $\kappa$ of $A$, a curve over $\kappa$ and essentially of finite type over it, and $R$ a regular prolongation of $A$ to $F$ with values in $\bar F$: a valuation subring $R.\mathrm{integers}$ of $F$ contracting to $A$ along $L\to F$, with a surjective residue homomorphism onto $\bar F$ whose kernel is the maximal ideal, compatible with $A\to\kappa\to\bar F$, and such that every $f\neq 0$ has an $L$-multiple in $R.\mathrm{integers}$ of nonzero residue; assume $R.\mathrm{integers}$ is the subring $\varphi^{-1}(\mathcal O_{X,\eta})$ of $F$, written `SemistableModel.localRing X φ η`. Let $Q$ be a place of $\bar F/\kappa$ (a valuation subring $\neq\top$ containing $\kappa$ and a principal ideal ring). Assume (smooth reading) that every closed point $x$ of $X$ over the closed point of $A$ with $\eta\rightsquigarrow x$ such that every $f\in R.\mathrm{integers}\cap\varphi^{-1}(\mathcal O_{X,x})$ has residue in $Q$ lies in the smooth locus of $\mathrm{toBase}$; that $D\subseteq\mathrm{Place}(L,F)$ and $z\in F$ satisfy `R.IsResidueDisc Q D z`, i.e. $z$ is a disc coordinate for $D$ at $Q$ (each $P\in D$ is rational with $z\in\mathcal O_P$ and $|z(P)|<1$; $z\in R.\mathrm{integers}$ with $\operatorname{ord}_Q$ of its residue equal to $1$; each $c\in L$ with $|c|<1$ is $z(P)$ for exactly one $P\in D$; $\operatorname{ord}_P(z-z(P))=1$ for $P\in D$; and any $f\neq 0$ with $\operatorname{ord}_P f=0$ on $D$ has $|f(P)|$ constant on $D$ equal to $|c|$ for some $c\neq 0$), together with the pointwise compatibility of residues at $Q$ and the degree law relating $\operatorname{ord}_Q$ of a residue to the sum of the orders over $D$; and (dimension) that for every non-closed point $\eta_1$ over the closed point of $A$, every $y\neq\eta_1$ with $\eta_1\rightsquigarrow y$ is closed. Then there is $x\in X$ over the closed point of $A$, closed, with $\eta\rightsquigarrow x$, read by $Q$ in the above sense, and such that for every $P\in D$ and every $f\in\varphi^{-1}(\mathcal O_{X,x})$ one has $f\in\mathcal O_P$, the value $P.\mathrm{evalAt}\,f\in L$ lies in $A$, and this value is a unit of $A$ if and only if $f$ is invertible in $\varphi^{-1}(\mathcal O_{X,x})$; that is, $f\mapsto f(P)$ is a local homomorphism $\varphi^{-1}(\mathcal O_{X,x})\to A$ for all $P\in D$.
--
--   This is the statement that a residue disc $(D,z)$ of the place $Q$ on the reduction $\bar F$ is contained in the formal fibre of a single closed point of the special fibre of $X$, namely the centre of $Q$ on the component corresponding to $\eta$, under the assumption that that centre is a smooth point of $X\to\operatorname{Spec}A$. It feeds the smooth-centre theorem [`AlgebraicCurve.exists_smoothCentre_of_isResidueDisc_of_reads_smooth`](thm.html#AlgebraicCurve.exists_smoothCentre_of_isResidueDisc_of_reads_smooth), where the smooth-reading hypothesis is discharged on the consumer side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_forall_specializes_of_isResidueDisc_of_reads_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_forall_specializes_of_isResidueDisc_of_reads_smooth
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
    (η : X) (hη : toBase.base η = closedPoint ↥A) (hηnc : ∃ y : X, η ⤳ y ∧ y ≠ η)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    [IsCurveOver (ResidueField ↥A) Fbar] [Algebra.EssFiniteType (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (Q : Place (ResidueField ↥A) Fbar)

    (hsmQ : ∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → η ⤳ x →
      (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring) →
      x ∈ toBase.smoothLocus)
    (D : Set (Place L F)) (z : F) (hD : R.IsResidueDisc Q D z)
    (hdim : ∀ η₁ y : X, toBase.base η₁ = closedPoint ↥A → (∃ y' : X, η₁ ⤳ y' ∧ y' ≠ η₁) → η₁ ⤳ y → y ≠ η₁ →
      ∀ y' : X, y ⤳ y' → y' = y) :
    ∃ x : X, toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧ η ⤳ x ∧
      (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring) ∧
      ∀ P : Place L F, P ∈ D →
        (∀ f : F, f ∈ SemistableModel.localRing X φ x →
          f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
            (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1)) := by sorry
