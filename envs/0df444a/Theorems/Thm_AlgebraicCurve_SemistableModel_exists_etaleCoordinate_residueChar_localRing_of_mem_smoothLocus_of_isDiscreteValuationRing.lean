-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing
-- name    : AlgebraicCurve.SemistableModel.exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/86919256-8503-595f-b51a-66a699746524
-- title:
--   Étale coordinate at a smooth closed special point over a DVR
-- statement:
--   Let $A$ be a discrete valuation ring which is a domain, $\varpi \in A$ an element with $\mathfrak m_A = (\varpi)$, and suppose the residue field $\kappa = A/\mathfrak m_A$ is algebraically closed; let $L$ be an $A$-algebra which is a field and a fraction field of $A$, and $F$ a field extension of $L$ which is a curve over $L$ in the project's sense, i.e. every nonzero element of $F$ has a degree-zero divisor recording its orders at all places (valuation subrings of $F$, proper, containing $L$ and principal ideal rings), each place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$. Let $X$ be an integral scheme with a morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$ that is locally of finite presentation, and let $\varphi : F \xrightarrow{\sim} K(X)$ be a ring isomorphism compatible with the two maps from $A$, namely $\varphi(a\cdot 1)$ equals the germ at the generic point of the image of $a$ under the structure morphism on global sections. Let $x \in X$ satisfy: its image is the closed point of $\operatorname{Spec} A$, the only $y$ with $x \rightsquigarrow y$ is $x$ itself, and $x$ lies in the smooth locus of $\mathrm{toBase}$. Write $S \subseteq F$ for the subring obtained as the image of $\mathcal O_{X,x} \to K(X) \xrightarrow{\varphi^{-1}} F$. Then there are ring homomorphisms $\varphi_T : A[T] \to S$ and $\chi : S \to \kappa$ such that: the image of $A$ in $F$ lies in $S$ and $\varphi_T$ sends the constant $a$ to it; $\chi \circ \varphi_T$ on constants is the residue map of $A$; $\chi(\varphi_T(T)) = 0$; for some local ring structure on $S$ one has $\ker \chi = \mathfrak m_S = (\varphi_T(\varpi), \varphi_T(T))$; $\chi$ is surjective; $\varphi_T$ is formally smooth, formally unramified and essentially of finite type; $\varphi_T(T) \notin (\varphi_T(\varpi))$; and every $f \in F$ is of the form $g/h$ with $g, h \in S$, $h \neq 0$.
--
--   This packages the local structure of an integral model at a closed point of the special fibre lying in the smooth locus: regular parameters $(\varpi, t)$ at such a point together with the resulting étale coordinate $A[T] \to \mathcal O_{X,x}$, $T \mapsto t$, and the residue character onto $\kappa$, all expressed through the copy of $\mathcal O_{X,x}$ inside the function field $F$. It is used in the comparison of a two-chart integral model with its charts at smooth points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    [IsAlgClosed (ResidueField A)]
    {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : A, φ (algebraMap L F (algebraMap A L a)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus) :
    ∃ (φT : Polynomial A →+* ↥(SemistableModel.localRing X φ x))
      (χ : ↥(SemistableModel.localRing X φ x) →+* ResidueField A),
      (∀ a : A, algebraMap L F (algebraMap A L a) ∈ SemistableModel.localRing X φ x) ∧
      (∀ a : A, ((φT (Polynomial.C a) : ↥(SemistableModel.localRing X φ x)) : F) = algebraMap L F (algebraMap A L a)) ∧
      (∀ a : A, χ (φT (Polynomial.C a)) = IsLocalRing.residue A a) ∧
      χ (φT Polynomial.X) = 0 ∧
      (∃ _ : IsLocalRing ↥(SemistableModel.localRing X φ x),
        RingHom.ker χ = IsLocalRing.maximalIdeal ↥(SemistableModel.localRing X φ x) ∧
        IsLocalRing.maximalIdeal ↥(SemistableModel.localRing X φ x) = Ideal.span {φT (Polynomial.C ϖ), φT Polynomial.X}) ∧
      Function.Surjective χ ∧
      φT.FormallySmooth ∧ φT.FormallyUnramified ∧ φT.EssFiniteType ∧
      φT Polynomial.X ∉ Ideal.span {φT (Polynomial.C ϖ)} ∧
      (∀ f : F, ∃ g h : ↥(SemistableModel.localRing X φ x), (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) := by sorry
