-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_smoothPointRing_mem_iff_and_locality_and_residue_surjective_of_mem_smoothLocus_of_isProper
-- name    : AlgebraicCurve.exists_smoothPointRing_mem_iff_and_locality_and_residue_surjective_of_mem_smoothLocus_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/577534cd-3b82-5c9f-affd-d0db5ddce453
-- title:
--   Reading place, locality and residue surjectivity at a smooth point
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring that is proper ($A\neq L$), henselian, and of rank one in the form: for $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ there is $n$ with $b\mid a^{n}$. Let $F/L$ be a field satisfying the project's `IsCurveOver` (principal divisors of degree zero, residue fields of all places finite over $L$, and $\Omega_{F/L}$ free of rank one over $F$) and essentially of finite type over $L$. Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism to $\operatorname{Spec}A$, together with an isomorphism $\varphi\colon F\simeq K(X)$ compatible with the structural map of $A$ into the function field. Let $x$ lie over the closed point of $A$, be closed (it specialises only to itself) and lie in the smooth locus; let $\eta\neq x$ also lie over the closed point and specialise to $x$. Let $Fbar$ be a field over the residue field of $A$ and $R$ a regular prolongation of $A$ to $F$ with reduced field $Fbar$: a valuation subring $R.\mathrm{integers}\subseteq F$ with a surjective homomorphism $R.\mathrm{residue}$ onto $Fbar$ whose kernel is the maximal ideal, inducing $A$ on $L$, compatible with the residue map of $A$, and with every nonzero $f\in F$ scalable by some $c\in L$ into the integers with nonzero reduction; assume $R.\mathrm{integers}$, as a subring of $F$, is the image $\mathcal O_{X,\eta}\subseteq F$ under $\varphi^{-1}$. Put $S:=\mathcal O_{X,x}\subseteq F$, the image of the stalk at $x$ in $F$. The conclusion asserts the existence of a place $Q$ of $Fbar$ over the residue field of $A$ (a proper valuation subring containing that residue field and a principal ideal ring) and a set $D$ of places of $F/L$ such that: (i) every $f\in S$ lies in $R.\mathrm{integers}$ and its reduction lies in $Q$; (ii) $Q$ is the only place of $Fbar$ with property (i); (iii) $D$ consists exactly of those places $P$ of $F/L$ for which every $f\in S$ lies in $P$, has $P.\mathrm{evalAt}\,f\in A$, and $P.\mathrm{evalAt}\,f$ is a unit of $A$ precisely when $f$ is invertible in $S$; (iv) any $f\in R.\mathrm{integers}$ lying in every $P\in D$ already lies in $S$; and (v) every element of $Q$ is the reduction of some element of $S$. Clause (iii) pins down $D$ by the stated condition rather than adding information; the content lies in (i), (ii), (iv), (v).
--
--   This is the statement that the formal fibre of a smooth closed point of a proper flat model over a henselian rank-one base is a residue disc: the local ring at $x$ reads off a single place $Q$ of the reduced field, is cut out inside the prolongation by the places specialising to $x$, and surjects onto the valuation ring of $Q$. It is a trimmed form of the full smooth-point package, shaped for the assembly of semistable models of modular curves, and is used by the descent constructions for semistable coverings at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_smoothPointRing_mem_iff_and_locality_and_residue_surjective_of_mem_smoothLocus_of_isProper.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_smoothPointRing_mem_iff_and_locality_and_residue_surjective_of_mem_smoothLocus_of_isProper
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
    ∃ (Q : Place (ResidueField ↥A) Fbar) (D : Set (Place L F)),

      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) ∧

      (∀ P : Place L F, P ∈ D ↔
        ∀ f : F, f ∈ S → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ S, f * g = 1)) ∧

      (∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) ∧

      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ R.integers), f ∈ S ∧ R.residue ⟨f, hf⟩ = g) := by sorry
