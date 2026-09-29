-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing
-- name    : AlgebraicCurve.SemistableModel.exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/0239e8f8-094a-5c10-b74b-18570e95ff20
-- title:
--   Parameters (varpi,t) at a smooth closed point of the special fibre
-- statement:
--   Let $A$ be a discrete valuation ring which is a domain, let $\varpi \in A$ generate the maximal ideal (so $\mathfrak{m}_A = (\varpi)$), and assume the residue field of $A$ is algebraically closed. Let $L$ be a field which is a fraction field of $A$, and let $F$ be a field extension of $L$ satisfying `IsCurveOver L F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place of $F/L$ is $\operatorname{ord}_v f$, each place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$. Let $X$ be a scheme (in universe $0$) with a morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$, with $X$ integral and $\mathrm{toBase}$ locally of finite presentation, and let $\varphi : F \cong X$'s function field be a ring isomorphism compatible with the base in the sense that $\varphi(\text{image of } a \in A \text{ in } F)$ is, for every $a$, the germ at the generic point of the image of $a$ under $A \to \Gamma(X, \mathcal{O}_X)$ (the map `baseToFunctionField`). Let $x \in X$ be a point lying over the closed point of $\operatorname{Spec} A$, such that the only $y$ to which $x$ specialises is $x$ itself (i.e. $x$ is closed), and such that $x$ lies in the smooth locus of $\mathrm{toBase}$. Write $c : A \to \mathcal{O}_{X,x}$ for the composite of $A \cong \Gamma(X,\mathcal{O}_X)$'s structural map with the germ map at $x$. Then $\mathcal{O}_{X,x}$ is a domain, $c$ is formally smooth and essentially of finite type, the composite $A \to \mathcal{O}_{X,x} \to \kappa(x)$ onto the residue field is surjective, and there exists $t \in \mathcal{O}_{X,x}$ with $\mathfrak{m}_{X,x} = (c(\varpi), t)$ and $t \notin (c(\varpi))$.
--
--   This is the local description of a relative curve over a discrete valuation ring at a smooth closed point of the special fibre: the local ring is two-dimensional regular with regular system of parameters $(\varpi, t)$, the residue field is that of $A$ (Hilbert's Nullstellensatz, the base residue field being algebraically closed), and $t$ reduces to a uniformiser of the local ring of the fibre. It serves as the input to the construction of an étale coordinate at such a point, which is where it is cited; the relative dimension one needed for the parameter count comes from $\dim_F \Omega_{F/L} = 1$ via [`AlgebraicCurve.SemistableModel.finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension`](thm.html#AlgebraicCurve.SemistableModel.finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing
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
    IsDomain (X.presheaf.stalk x) ∧
    c.FormallySmooth ∧ c.EssFiniteType ∧
    Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp c) ∧
    ∃ t : X.presheaf.stalk x,
      maximalIdeal (X.presheaf.stalk x) = Ideal.span {c ϖ, t} ∧ t ∉ Ideal.span {c ϖ} := by sorry
