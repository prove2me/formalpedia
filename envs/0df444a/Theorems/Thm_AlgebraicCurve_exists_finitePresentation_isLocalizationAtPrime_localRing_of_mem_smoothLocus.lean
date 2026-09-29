-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus
-- name    : AlgebraicCurve.exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/ca0a6a6a-ec5f-5d6f-9be9-66d7cbda8428
-- title:
--   Local ring at a smooth special point: localisation of a finitely presented flat algebra
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring such that for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ some power $a^n$ is divisible by $b$, with $A \neq L$ as a subset of $L$, and with $A$ henselian. Let $F$ be a field extension of $L$ which is a curve over $L$ in the project's sense (every nonzero element has a degree-zero divisor recording its orders at all places, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank $1$ over $F$) and essentially of finite type over $L$. Let $X$ be an integral scheme and $\mathrm{toBase} : X \to \operatorname{Spec} A$ proper, flat and locally of finite presentation, together with a ring isomorphism $\varphi : F \cong$ the function field of $X$ carrying $A \to L \to F$ to the canonical map $A \to \mathcal{O}_{X,\text{generic}}$ induced by $\mathrm{toBase}$. Let $x \in X$ lie over the closed point of $A$, specialise only to itself, and lie in the smooth locus of $\mathrm{toBase}$, and let $\eta \in X$ lie over the closed point with $\eta \rightsquigarrow x$ and $\eta \neq x$. Let $\bar{F}$ be an extension of the residue field of $A$ and $R$ a regular prolongation of $A$ to $F$ with values in $\bar{F}$, that is, a valuation subring $R.\mathrm{integers}$ of $F$ contracting to $A$ along $L \to F$, equipped with a surjection onto $\bar{F}$ with kernel its maximal ideal, compatible with the residue map of $A$, and such that every nonzero $f \in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero residue; assume $R.\mathrm{integers}$ equals the image in $F$ under $\varphi^{-1}$ of the stalk $\mathcal{O}_{X,\eta}$ inside the function field. Put $S \subseteq F$ for the image under $\varphi^{-1}$ of $\mathcal{O}_{X,x}$. The conclusion asserts the existence of a ring map $\iota : A \to S$ sending $a$ to the image of $a$ in $F$, a commutative ring $B$ with an $A$-algebra structure and a $B$-algebra structure on $S$, and a prime ideal $\mathfrak{n} \subseteq B$, such that, $S$ being viewed as an $A$-algebra via $\iota$: $B$ is a finitely presented $A$-algebra, $\mathfrak{n}$ contracts to the maximal ideal of $A$, $A \to B \to S$ is a scalar tower, $S$ is a localisation of $B$ at $\mathfrak{n}$, $S$ is flat as an $A$-module, and for every $h \in S$ with $h \neq 0$ and $h^{-1} \in R.\mathrm{integers}$, the class of $h$ in $S/\mathfrak{m}_A S$ is a non-zero-divisor and $S/(h, \mathfrak{m}_A S)$ is a finite $A$-module.
--
--   This is the passage from the scheme-theoretic model $X \to \operatorname{Spec} A$ to pure commutative algebra: the local ring at a smooth closed point of the special fibre is exhibited as a localisation of a finitely presented flat $A$-algebra, with regularity and cofiniteness on the fibre for units of the component through $\eta$. It supports the Weierstrass-type preparation arguments, being cited by [`AlgebraicCurve.exists_monic_eval2_eq_mul_of_inv_mem_integers_of_ord_eq_one_of_mem_smoothLocus`](thm.html#AlgebraicCurve.exists_monic_eval2_eq_mul_of_inv_mem_integers_of_ord_eq_one_of_mem_smoothLocus) and [`AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus`](thm.html#AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus); the regularity of the fibre comes from [`AlgebraicCurve.SemistableModel.isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus`](thm.html#AlgebraicCurve.SemistableModel.isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus
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
    ∃ (ι : ↥A →+* ↥S) (_ : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
      (B : Type) (_ : CommRing B) (_ : Algebra ↥A B) (_ : Algebra B ↥S) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      letI : Algebra ↥A ↥S := ι.toAlgebra
      Algebra.FinitePresentation ↥A B ∧ 𝔫.comap (algebraMap ↥A B) = maximalIdeal ↥A ∧
      IsScalarTower ↥A B ↥S ∧ IsLocalization.AtPrime ↥S 𝔫 ∧ Module.Flat ↥A ↥S ∧
      ∀ (h : F) (hh : h ∈ S), h ≠ 0 → h⁻¹ ∈ R.integers →
        Ideal.Quotient.mk ((maximalIdeal ↥A).map (algebraMap ↥A ↥S)) ⟨h, hh⟩ ∈
            nonZeroDivisors (↥S ⧸ (maximalIdeal ↥A).map (algebraMap ↥A ↥S)) ∧
          Module.Finite ↥A (↥S ⧸ (Ideal.span ({⟨h, hh⟩} : Set ↥S) ⊔ (maximalIdeal ↥A).map (algebraMap ↥A ↥S))) := by sorry
