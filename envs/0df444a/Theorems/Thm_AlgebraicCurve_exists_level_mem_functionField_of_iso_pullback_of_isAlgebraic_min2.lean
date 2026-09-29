-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min2
-- name    : AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/ade161d8-9611-54f4-a221-d4445d2dc6c2
-- title:
--   Descent of finitely many functions to a discrete valuation level
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring satisfying the divisibility condition that for all $a, b \in A$ with $a$ in the maximal ideal of $A$ and $b \neq 0$ there is an $n \in \mathbb{N}$ with $b \mid a^{n}$. Let $X$ be an integral scheme with a morphism $\mathrm{toBase} \colon X \to \operatorname{Spec} A$ that is proper, flat and locally of finite presentation. Let $A_0$ be a discrete valuation domain with uniformiser $\varpi_0$ (so the maximal ideal of $A_0$ is $(\varpi_0)$), and $\iota_0 \colon A_0 \to A$ an injective local ring homomorphism such that every element of $A$ is algebraic over the image subring $\iota_0(A_0)$. Let $X_0$ be an integral scheme with $\mathrm{toBase}_0 \colon X_0 \to \operatorname{Spec} A_0$ proper, flat and locally of finite presentation, and let $\mathrm{iso} \colon X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ be an isomorphism whose composite with the second projection is $\mathrm{toBase}$. Finally let $f \colon \mathrm{Fin}\, n \to K(X)$ be a finite family of elements of the function field of $X$, i.e. of the stalk at the generic point. The conclusion asserts the existence of: a discrete valuation domain $A_1$ with uniformiser $\varpi_1$; local ring homomorphisms $\iota_1' \colon A_0 \to A_1$ and $\iota_1 \colon A_1 \to A$ with $\iota_1$ injective and $\iota_1 \circ \iota_1' = \iota_0$; an integral scheme $X_1$ with morphisms $f_1 \colon X_1 \to \operatorname{Spec} A_1$ and $g_1 \colon X_1 \to X_0$ forming a pullback square over $\operatorname{Spec}(\iota_1')$, so that $X_1$ is the base change of $X_0$ to $A_1$; an isomorphism $e_1 \colon X \cong X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$ whose composite with the second projection is $\mathrm{toBase}$ and whose composite $\pi$ with the first projection, followed by $g_1$, agrees with $\mathrm{iso}$ followed by the first projection to $X_0$; the statement $\mathrm{hgen}$ that $\pi$ sends the generic point of $X$ to the generic point of $X_1$; and a family $u \colon \mathrm{Fin}\, n \to K(X_1)$ such that for each $i$ the element $f_i$ is the image of $u_i$ under the stalk map of $\pi$ at the generic point of $X$, precomposed with the specialisation map of the structure presheaf of $X_1$ given by $\mathrm{hgen}$.
--
--   This is the descent-to-finite-level step for the base ring: a finite family of rational functions on a proper flat finitely presented model over a rank-one valuation ring, which is itself a base change from a discrete valuation subring $A_0$, already lives on the base change of the model to a single intermediate discrete valuation ring $A_1$ finite over $A_0$ inside $A$. It is used in the analysis of stalks of such models at points of the smooth locus, where one must work over a discrete valuation ring rather than over the (possibly non-noetherian) valuation ring $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min2.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.exists_level_mem_functionField_of_iso_pullback_of_isAlgebraic_min2
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
