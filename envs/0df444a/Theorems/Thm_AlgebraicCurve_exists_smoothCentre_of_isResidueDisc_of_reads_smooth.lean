-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_smoothCentre_of_isResidueDisc_of_reads_smooth
-- name    : AlgebraicCurve.exists_smoothCentre_of_isResidueDisc_of_reads_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/acc720e2-0b04-5121-87ab-fa1083794853
-- title:
--   Residue disc has a smooth centre and is its formal fibre
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a henselian valuation subring with $A\neq L$ satisfying the rank-one condition that for $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ one has $b\mid a^{n}$ for some $n$. Let $F$ be a field over $L$ which is a curve over $L$ in the sense of `IsCurveOver` (principal divisors of degree $0$ exist, all places have residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type. Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism `toBase` to $\operatorname{Spec} A$, all of whose stalks are integrally closed, together with a ring isomorphism $\varphi\colon F\to K(X)$ compatible with the structural map $A\to K(X)$, and let $\eta\in X$ lie over the closed point of $A$ and admit a strictly larger specialisation. Let $\bar F$ be a curve over the residue field $\kappa$ of $A$, essentially of finite type, and $R$ a regular prolongation of $A$ to $F$ with values in $\bar F$ (a valuation subring $R.\mathrm{integers}$ of $F$ with a surjective homomorphism $R.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, inducing $\kappa\to\bar F$ on $A$, with $\mathrm{algebraMap}\,x\in R.\mathrm{integers}\iff x\in A$ and every nonzero $f\in F$ scalable into $R.\mathrm{integers}$ with nonzero residue), whose ring of integers is, as a subring of $F$, the image $\mathcal O_{X,\eta}\subseteq F$ given by `SemistableModel.localRing`. Let $Q$ be a place of $\bar F/\kappa$. Assume that every closed point $x$ of $X$ over the closed point of $A$ with $\eta\rightsquigarrow x$ which is read by $Q$ — meaning $R.\mathrm{residue}\,f\in\mathcal O_Q$ for all $f\in R.\mathrm{integers}$ lying in the local ring at $x$ — belongs to the smooth locus of `toBase`. Let $D$ be a set of places of $F/L$ and $z\in F$ with `R.IsResidueDisc Q D z`, i.e. $z$ is a disc coordinate for $(Q,D)$, $D$ is pointwise compatible with $Q$, and the degree law holds. Assume finally that for every non-closed point $\eta_1$ over the closed point of $A$, every strictly larger specialisation of $\eta_1$ is closed. Then there is a closed point $x$ of $X$ over the closed point of $A$, lying in the smooth locus, with $\eta\rightsquigarrow x$ and $\eta\neq x$, read by $Q$; moreover any place $Q'$ of $\bar F/\kappa$ reads at most one closed point of $X$ over the closed point of $A$ that is a specialisation of $\eta$; and a place $P$ of $F/L$ lies in $D$ if and only if every $f$ in the local ring of $X$ at $x$ (viewed in $F$) lies in $\mathcal O_P$ and has $P.\mathrm{evalAt}\,f\in A$, this value being a unit of $A$ exactly when $f$ is invertible in that local ring.
--
--   This identifies the centre of a residue disc on a model of a curve over a henselian valuation ring: the disc $D$ is precisely the formal fibre of a smooth closed point $x$ of the special fibre specialising from $\eta$. It is used in the assembly of the semistable model of the full-level modular curve, where the smooth-reading hypothesis is discharged from data at the nodes of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_smoothCentre_of_isResidueDisc_of_reads_smooth.lean

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

theorem AlgebraicCurve.exists_smoothCentre_of_isResidueDisc_of_reads_smooth
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
    ∃ x : X, toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧ x ∈ toBase.smoothLocus ∧ η ⤳ x ∧ η ≠ x ∧
      (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring) ∧

      (∀ (Q' : Place (ResidueField ↥A) Fbar) (x₁ x₂ : X),
        toBase.base x₁ = closedPoint ↥A → (∀ y : X, x₁ ⤳ y → y = x₁) →
        toBase.base x₂ = closedPoint ↥A → (∀ y : X, x₂ ⤳ y → y = x₂) → η ⤳ x₁ → η ⤳ x₂ →
        (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₁ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) →
        (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₂ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) →
          x₁ = x₂) ∧
      ∀ P : Place L F, P ∈ D ↔
        ∀ f : F, f ∈ SemistableModel.localRing X φ x →
          f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
            (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1) := by sorry
