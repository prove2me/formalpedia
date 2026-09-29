-- Prove2me | Theorems.Thm_AlgebraicCurve_algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes
-- name    : AlgebraicCurve.algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/f9ad5669-023f-5209-be34-f83aa5d8a787
-- title:
--   Constants and denominators in the local ring at x
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring satisfying: for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$; $A \neq L$ as a subset of $L$; and $A$ is a henselian local ring. Let $F$ be a field extension of $L$ which is a curve over $L$ in the project's sense (every nonzero element of $F$ has a degree-zero divisor recording its order at all places, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$. Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism `toBase` to $\operatorname{Spec} A$, and $\varphi : F \cong K(X)$ a ring isomorphism carrying $A \to L \to F$ to the composite $A \to \Gamma(X,\mathcal O_X) \to \mathcal O_{X,\text{gen}} \to K(X)$ given by `SemistableModel.baseToFunctionField`. Let $x \in X$ lie over the closed point of $A$, have no proper specialisation (every $y$ with $x \rightsquigarrow y$ equals $x$) and lie in the smooth locus of `toBase`; let $\eta \neq x$ lie over the closed point with $\eta \rightsquigarrow x$. Let $Fbar$ be a field over the residue field of $A$ and $R$ a regular prolongation of $A$ to $F$ with values in $Fbar$ (a valuation subring $R.\text{integers}$ of $F$ meeting $L$ exactly in $A$, equipped with a surjective residue map to $Fbar$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero element of $F$ can be scaled by $L$ into the subring with nonzero residue), and assume $R.\text{integers}$, as a subring of $F$, equals $\varphi^{-1}(\mathcal O_{X,\eta})$ inside $F$. Put $S := \varphi^{-1}(\mathcal O_{X,x}) \subseteq F$, the image of the stalk at $x$ in $F$. Then (i) $\operatorname{algebraMap}_{L,F}(a) \in S$ for every $a \in A$, and (ii) for every $f \in R.\text{integers}$ there are $g, h \in S$ with $h \neq 0$, $h^{-1} \in R.\text{integers}$ and $f h = g$.
--
--   This is the scheme-theoretic bookkeeping step saying that on a model of $F$ over $A$ the constants $A$ land in the local ring at a closed point $x$ of the special fibre, and that the local ring at a generisation $\eta$ of $x$ — identified with the valuation ring of a regular prolongation $R$ — consists of fractions with numerator and denominator in $\mathcal O_{X,x}$, the denominator being invertible in $R$. It feeds the comparison of $\mathcal O_{X,x}$ with $R$ used in [`AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus`](thm.html#AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.algebraMap_mem_localRing_and_exists_mul_eq_of_mem_integers_of_specializes
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
    (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
    (∀ f : F, f ∈ R.integers → ∃ g h : F, g ∈ S ∧ h ∈ S ∧ h ≠ 0 ∧ h⁻¹ ∈ R.integers ∧ f * h = g) := by sorry
