-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_formallySmooth_isLocalizationAtPrime_localRing_of_mem_smoothLocus
-- name    : AlgebraicCurve.exists_formallySmooth_isLocalizationAtPrime_localRing_of_mem_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/f11052f5-63c8-5fc9-bd76-96036ca52106
-- title:
--   Local ring at a smooth special point is a localisation
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring which is a henselian local ring, which is not all of $L$, and which satisfies the rank-one type condition that for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$. Let $F$ be a field extension of $L$ which is essentially of finite type over $L$ and satisfies `IsCurveOver L F`: every nonzero $f \in F$ has a degree-zero divisor recording its orders at all places of $F/L$, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$. Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism `toBase` to $\operatorname{Spec} A$, and let $\varphi : F \cong X$'s function field be a ring isomorphism compatible with the structure maps, i.e. $\varphi(\text{image of } a)$ equals the image of $a \in A$ under `SemistableModel.baseToFunctionField toBase`. Let $x \in X$ lie over the closed point of $\operatorname{Spec} A$, be closed in $X$ (any $y$ in the closure of $\{x\}$ equals $x$), and lie in `toBase.smoothLocus`; let $\eta \neq x$ be a further point over the closed point with $x$ in the closure of $\{\eta\}$. Let $\bar F$ be a field extension of the residue field of $A$ and $R$ a `RegularProlongation` of $A$ to $F$ with residue field $\bar F$ — a valuation subring of $F$ meeting $L$ exactly in $A$, equipped with a surjection onto $\bar F$ with kernel its maximal ideal, compatible with the residue map of $A$, and such that every nonzero $f \in F$ has an $L$-multiple lying in it with nonzero residue — and assume that its underlying subring is `SemistableModel.localRing X φ η`, the image in $F$ of the local ring $\mathcal{O}_{X,\eta}$ under $\varphi^{-1}$. Put $S :=$ `SemistableModel.localRing X φ x`, the image in $F$ of $\mathcal{O}_{X,x}$. The conclusion asserts the existence of a ring homomorphism $\iota : A \to S$ whose composite with the inclusion $S \subseteq F$ is $a \mapsto \operatorname{algebraMap} L F(a)$, a commutative ring $B$ with $A$-algebra and $B$-algebra-on-$S$ structures, and a prime ideal $\mathfrak{n} \subseteq B$, such that, with $A \to S$ given by $\iota$: $B$ is of finite presentation and formally smooth over $A$, the contraction of $\mathfrak{n}$ along $A \to B$ is the maximal ideal of $A$, $A \to B \to S$ is a scalar tower, $S$ is the localisation of $B$ at $\mathfrak{n}$, and $S$ is flat as an $A$-module.
--
--   This is the local bridge between the scheme-theoretic model and commutative algebra: at a closed point $x$ of the special fibre lying in the smooth locus, the subring $\mathcal{O}_{X,x}$ of $F$ is exhibited as the localisation at a prime over $\mathfrak{m}_A$ of a finitely presented, formally smooth $A$-algebra, and is in particular flat over $A$. It is used in the construction of sections through such a point, in [`AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus`](thm.html#AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus), where the smooth presentation together with henselianity of $A$ produces the required lift.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_formallySmooth_isLocalizationAtPrime_localRing_of_mem_smoothLocus.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_formallySmooth_isLocalizationAtPrime_localRing_of_mem_smoothLocus
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
      Algebra.FinitePresentation ↥A B ∧ Algebra.FormallySmooth ↥A B ∧ 𝔫.comap (algebraMap ↥A B) = maximalIdeal ↥A ∧
      IsScalarTower ↥A B ↥S ∧ IsLocalization.AtPrime ↥S 𝔫 ∧ Module.Flat ↥A ↥S := by sorry
