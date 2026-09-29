-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_isDiscreteValuationRing_stalk_quotient_span_of_mem_smoothLocus_of_isDiscreteValuationRing
-- name    : AlgebraicCurve.SemistableModel.isDiscreteValuationRing_stalk_quotient_span_of_mem_smoothLocus_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/dac98802-27e4-5edf-b000-162d5fd92b1e
-- title:
--   Stalk mod uniformiser at a smooth closed special point
-- statement:
--   Let $A$ be a discrete valuation domain with uniformiser $\varpi$, so that $\mathfrak m_A = (\varpi)$, and assume the residue field of $A$ is algebraically closed; let $L$ be a field which is an $A$-algebra realised as the fraction field of $A$, and let $F$ be a field extension of $L$ satisfying `IsCurveOver L F`, i.e. every nonzero element of $F$ has a degree-zero divisor recording its order at every place of $F/L$, each place of $F/L$ has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$. Let $X$ be an integral scheme with a morphism $\mathtt{toBase} : X \to \operatorname{Spec} A$ that is locally of finite presentation, and let $\varphi : F \xrightarrow{\ \sim\ } K(X)$ be a ring isomorphism onto the function field of $X$ which carries the image of each $a \in A$ in $F$ to the image of $a$ under the map $A \to K(X)$ obtained from $\mathtt{toBase}$ on global sections followed by the germ at the generic point. Let $x \in X$ be a point lying over the closed point of $\operatorname{Spec} A$, such that the only point to which $x$ specialises is $x$ itself, and lying in the smooth locus of $\mathtt{toBase}$. Writing $c : A \to \mathcal O_{X,x}$ for the structure map (global sections of $\mathtt{toBase}$ followed by the germ at $x$), the conclusion is that $\mathcal O_{X,x}/(c\,\varpi)$ is an integral domain and a discrete valuation ring.
--
--   This is the local statement that a relative curve over a discrete valuation ring has, at a closed point of its special fibre lying in the smooth locus, regular local fibre ring of dimension one: the fibre $\mathcal O_{X,x}/\mathfrak m_A\mathcal O_{X,x}$ is a discrete valuation ring. It supplies the domain-and-discrete-valuation-ring input used in the analysis of two-chart integral models, where it feeds the construction of an étale coordinate at $x$ and a regular system of parameters $(\varpi, t)$ of $\mathcal O_{X,x}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_isDiscreteValuationRing_stalk_quotient_span_of_mem_smoothLocus_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.isDiscreteValuationRing_stalk_quotient_span_of_mem_smoothLocus_of_isDiscreteValuationRing
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
    let c : A →+* X.presheaf.stalk x :=
      (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    ∃ _ : IsDomain (X.presheaf.stalk x ⧸ Ideal.span {c ϖ}),
      IsDiscreteValuationRing (X.presheaf.stalk x ⧸ Ideal.span {c ϖ}) := by sorry
