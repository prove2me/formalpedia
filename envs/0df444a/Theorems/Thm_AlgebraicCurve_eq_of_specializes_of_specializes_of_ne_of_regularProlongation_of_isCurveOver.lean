-- Prove2me | Theorems.Thm_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver
-- name    : AlgebraicCurve.eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/8ee58b1d-7487-5d0a-8517-5e710c883132
-- title:
--   Specialisations of a non-closed special point are closed
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring which is henselian local, is not all of $L$, and satisfies: for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$. Let $F$ be a field extension of $L$ which is essentially of finite type and satisfies `IsCurveOver L F`, i.e. every nonzero $f \in F$ has a degree-zero divisor recording its orders at all places, every place of $F/L$ has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$. Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$, all of whose stalks are integrally closed, together with a ring isomorphism $\varphi : F \simeq K(X)$ carrying $A \to F$ to the canonical map $A \to K(X)$ obtained from $\mathrm{toBase}$. Let $\eta \in X$ lie over the closed point of $A$ and be non-closed (some $y \neq \eta$ lies in the closure of $\eta$). Let $\bar F$ be a field over $\kappa = \operatorname{ResidueField} A$ which is essentially of finite type and satisfies `IsCurveOver` $\kappa$ $\bar F$ in the same sense, and let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$: a valuation subring $R.\mathrm{integers}$ of $F$ whose preimage in $L$ is $A$, equipped with a surjection onto $\bar F$ with kernel the maximal ideal, compatible with $A \to \kappa \to \bar F$, such that every nonzero $f \in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero residue. Assume the subring of $F$ underlying $R.\mathrm{integers}$ is the image in $F$ under $\varphi^{-1}$ of the stalk of $X$ at $\eta$. Then for any $y$ in the closure of $\eta$ with $y \neq \eta$, every $y'$ in the closure of $y$ equals $y$.
--
--   This is the point-set form of the statement that the special fibre of a flat proper model of a curve over a valuation ring of rank one has dimension one along the component $\overline{\{\eta\}}$: below a non-closed point of the special fibre there are only closed points. It is used in the proof of [`AlgebraicCurve.eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue`](thm.html#AlgebraicCurve.eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue), and its own proof invokes the finiteness of $F$ over $L\langle t\rangle$ for $t$ transcendental.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.eq_of_specializes_of_specializes_of_ne_of_regularProlongation_of_isCurveOver
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
    (y : X) (hy : η ⤳ y) (hyη : y ≠ η) (y' : X) (hy' : y ⤳ y') :
    y' = y := by sorry
