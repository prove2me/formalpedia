-- Prove2me | Theorems.Thm_AlgebraicCurve_eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue
-- name    : AlgebraicCurve.eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/4626d635-1665-5774-9cc6-4577b249bcc2
-- title:
--   Uniqueness of the centre of a place on a special fibre component
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring which is henselian, is not all of $L$, and satisfies the rank condition that for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$. Let $F$ be an $L$-algebra which is a field, essentially of finite type over $L$ and a curve over $L$ in the project's sense (every $F$-function has a degree-zero principal divisor supported by the $\mathrm{ord}$ of the places of $F/L$, each place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one). Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$ all of whose stalks are integrally closed, and let $\varphi : F \cong K(X)$ be a ring isomorphism carrying $\mathrm{algebraMap}_{L\to F}(a)$, for $a \in A$, to the image of $a$ in $K(X)$ under $\mathrm{SemistableModel.baseToFunctionField}$. Let $\eta \in X$ lie over the closed point of $A$ and not be closed in the sense that some $y \neq \eta$ lies in the closure of $\eta$. Let $\bar F$ be a field over the residue field $\kappa$ of $A$, essentially of finite type and a curve over $\kappa$ in the same sense, and let $R$ be a regular prolongation of $A$ in $F$ with reduced field $\bar F$: a valuation subring $R.\mathrm{integers}$ of $F$ meeting $L$ exactly in $A$, together with a surjective ring map $R.\mathrm{residue} : R.\mathrm{integers} \to \bar F$ with kernel the maximal ideal, compatible with $A \to \kappa \to \bar F$, and such that every nonzero $f \in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero residue; assume $R.\mathrm{integers}$ coincides, as a subring of $F$, with the image in $F$ under $\varphi^{-1}$ of the stalk $\mathcal O_{X,\eta}$ inside $K(X)$. Finally let $Q'$ be a place of $\bar F/\kappa$, that is, a valuation subring of $\bar F$, not all of $\bar F$, containing $\kappa$ and a principal ideal ring, and let $x_1,x_2 \in X$ both lie over the closed point of $A$, be closed (their only specialisations are themselves), and lie in the closure of $\eta$, and suppose that every $f \in R.\mathrm{integers}$ whose image lies in the subring of $F$ cut out by $\mathcal O_{X,x_i}$ has $R.\mathrm{residue}(f) \in Q'$, for $i = 1,2$. Then $x_1 = x_2$.
--
--   This is the uniqueness half of the statement that a place of the reduced field of a component of the special fibre has at most one centre among the closed points of that component; the curve hypotheses on $F/L$ and $\bar F/\kappa$ are what make the component one-dimensional, and the conclusion fails in higher relative dimension. It is used in the construction of the semistable model of the full-level modular covering, where node places of the charts are matched with the branch places at the nodes of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue
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
    [AlgebraicCurve.IsCurveOver (IsLocalRing.ResidueField ↥A) Fbar] [Algebra.EssFiniteType (IsLocalRing.ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (Q' : Place (ResidueField ↥A) Fbar) (x₁ x₂ : X)
    (hx₁ : toBase.base x₁ = closedPoint ↥A) (hx₁c : ∀ y : X, x₁ ⤳ y → y = x₁)
    (hx₂ : toBase.base x₂ = closedPoint ↥A) (hx₂c : ∀ y : X, x₂ ⤳ y → y = x₂)
    (h₁ : η ⤳ x₁) (h₂ : η ⤳ x₂)
    (hr₁ : ∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₁ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring)
    (hr₂ : ∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₂ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) :
    x₁ = x₂ := by sorry
