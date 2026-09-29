-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/a96a9ee5-9cb5-557f-8532-15a31374287e
-- title:
--   Normality of the base-changed stalk above an ordinary double point
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring satisfying: for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$ (a rank-one condition), and $A \neq L$ as a subset. Let $A_{0}$ be a discrete valuation domain, $\iota : A_{0} \to A$ an injective local ring homomorphism such that the composite of $\iota$ with the residue map of $A$ is surjective and every element of $A$ is algebraic over the image $\iota(A_{0})$, and let $\varpi_{0}$ generate the maximal ideal of $A_{0}$. Let $X_{0} \to \operatorname{Spec} A_{0}$ and $X \to \operatorname{Spec} A$ be morphisms with $X_{0}$, $X$ integral and both morphisms proper, flat and locally of finite presentation, together with an isomorphism $X \cong X_{0} \times_{\operatorname{Spec} A_{0}} \operatorname{Spec} A$ whose composite with the second projection is the given morphism $X \to \operatorname{Spec} A$. Let $y \in X$ lie over the closed point of $\operatorname{Spec} A$, admit no proper specialisation (every $z$ with $y \rightsquigarrow z$ equals $y$), and carry a branch: some $\eta \neq y$ over the closed point of $\operatorname{Spec} A$ with $\eta \rightsquigarrow y$. Let $y_{0} \in X_{0}$ be the image of $y$ under the first projection, with $\mathcal{O}_{X_{0},y_{0}}$ noetherian, and suppose for some $w \geq 1$ there is a ring isomorphism $$\widehat{\mathcal{O}}_{X_{0},y_{0}} \;\cong\; \widehat{A}_{0}[[u,v]]/(uv - \varpi_{0}^{\,w}),$$ where $\widehat{A}_{0}$ is the maximal-ideal-adic completion of $A_{0}$ and $u,v$ are the two power series variables, carrying the germ at $y_{0}$ of each $a \in A_{0}$ pulled back from the base to the class of the constant series $a$. Then the stalk $\mathcal{O}_{X,y}$ is integrally closed.
--
--   This is the ordinary-double-point case of the assertion that base change of a proper flat model along a local embedding of a discrete valuation ring into a rank-one valuation ring with the same residue field and algebraic extension remains normal at points of the special fibre. It feeds the general normality statement [`AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ordinaryDoublePoints_of_isDiscreteValuationRing_of_relDimOne`](thm.html#AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ordinaryDoublePoints_of_isDiscreteValuationRing_of_relDimOne) for models whose singularities are ordinary double points in relative dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)

    (y : X) (hy : toBase.base y = closedPoint ↥A) (hyc : ∀ z : X, y ⤳ z → z = y)

    (hbranch : ∃ η : X, η ⤳ y ∧ η ≠ y ∧ toBase.base η = closedPoint ↥A)
    (y₀ : X₀) (hy₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base y = y₀)
    [IsNoetherianRing (X₀.presheaf.stalk y₀)]
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk y₀)) (X₀.presheaf.stalk y₀) ≃+*
        (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
            MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk y₀) _
          ((X₀.presheaf.germ ⊤ y₀ trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))) :
    IsIntegrallyClosed (X.presheaf.stalk y) := by sorry
