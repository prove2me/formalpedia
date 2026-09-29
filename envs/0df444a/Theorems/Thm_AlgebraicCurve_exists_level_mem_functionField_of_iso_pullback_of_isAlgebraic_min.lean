-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min
-- name    : AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/336e982c-4172-5f2d-999a-e341bb778fdd
-- title:
--   Finite families of rational functions descend to a DVR level
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring such that for all $a,b \in A$ with $a$ in the maximal ideal of $A$ and $b \neq 0$ there is an $n$ with $b \mid a^{n}$. Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$. Let $A_0$ be a discrete valuation domain with uniformiser $\varpi_0$ generating its maximal ideal, and $\iota_0 : A_0 \to A$ an injective local homomorphism such that every element of $A$ is algebraic over the subring $\iota_0(A_0)$. Let $X_0$ be integral with $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ proper, flat and locally of finite presentation, and let $\mathrm{iso}$ identify $X$ with the fibre product of $\mathrm{toBase}_0$ along $\operatorname{Spec}(\iota_0)$ compatibly with the structure morphisms, i.e. $\mathrm{iso}$ followed by the second projection is $\mathrm{toBase}$. Let $x \in X$ lie over the closed point of $\operatorname{Spec} A$ and specialise only to itself, let $x_0$ be its image in $X_0$ under $\mathrm{iso}$ followed by the first projection, let $w \ge 1$, and suppose given a ring isomorphism $e$ from the adic completion of the local ring $\mathcal{O}_{X_0,x_0}$ at its maximal ideal onto the crossing model $\widehat{A_0}[[u,v]]/(uv - \varpi_0^{w})$, where $\widehat{A_0}$ is the adic completion of $A_0$ and $\varpi_0$ is read in $\widehat{A_0}$, such that for every $a \in A_0$ the image under $e$ of the completed germ at $x_0$ of the global section $\mathrm{toBase}_0^{\#}(a)$ is the class of the constant power series with value $a$. Then, for every finite family $f : \mathrm{Fin}\,n \to K(X)$ of elements of the function field of $X$ (the stalk at the generic point), there exist a discrete valuation domain $A_1$ with uniformiser $\varpi_1$ generating its maximal ideal, local homomorphisms $\iota_1' : A_0 \to A_1$ and $\iota_1 : A_1 \to A$ with $\iota_1$ injective and $\iota_1 \circ \iota_1' = \iota_0$, an integral scheme $X_1$ with morphisms $f_1 : X_1 \to \operatorname{Spec} A_1$ and $g_1 : X_1 \to X_0$ making $(g_1, f_1)$ a pullback square over $\mathrm{toBase}_0$ and $\operatorname{Spec}(\iota_1')$, and an isomorphism $e_1$ of $X$ with the fibre product of $f_1$ along $\operatorname{Spec}(\iota_1)$ such that $e_1$ followed by the second projection is $\mathrm{toBase}$ and the projection $p := e_1$ followed by the first projection satisfies $g_1 \circ p = \mathrm{iso}$ followed by the first projection; moreover $p$ carries the generic point of $X$ to the generic point of $X_1$, and there are $u : \mathrm{Fin}\,n \to K(X_1)$ with $f(i)$ the image of $u(i)$ under the map on function fields induced by $p$ (the stalk map at the generic point, preceded by the transport along the equality of points) for every $i$.
--
--   This is the statement that a finite family of rational functions on the base change $X = X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ of a crossing model already lives at a single finite level: one discrete valuation ring $A_1$ interpolating $A_0 \to A$ over which all the given functions are defined. It is used in the verification that the stalks of such base-changed models are integrally closed, namely by [`AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing), where normality is checked one finite family of elements at a time.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))
    {n : ℕ} (f : Fin n → X.functionField) :
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (ι₁' : A₀ →+* A₁) (_ : IsLocalHom ι₁') (ι₁ : A₁ →+* ↥A) (_ : IsLocalHom ι₁) (_ : Function.Injective ι₁)
      (_ : ι₁.comp ι₁' = ι₀) (ϖ₁ : A₁) (_ : maximalIdeal A₁ = Ideal.span {ϖ₁})
      (X₁ : Scheme.{0}) (_ : IsIntegral X₁) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (g₁ : X₁ ⟶ X₀)
      (_ : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι₁')))
      (e₁ : X ≅ Limits.pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
      (_ : e₁.hom ≫ Limits.pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase)
      (_ : (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ g₁ =
        iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
      (hgen : (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint X) = genericPoint X₁)
      (u : Fin n → X₁.functionField),
      ∀ i : Fin n, f i = ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint X)).hom
        ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (u i)) := by sorry
