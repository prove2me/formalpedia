-- Prove2me | Theorems.Thm_AlgebraicCurve_flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk
-- name    : AlgebraicCurve.flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/8ff43696-5122-52be-9caf-524006ae6198
-- title:
--   Flatness of the level projection and primes of the level stalk
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring such that for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$; let $F/L$ be essentially of finite type and a curve over $L$ in the project's sense (every nonzero function has a degree-zero principal divisor on the places of $F/L$, all place residue fields are finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$). Let $\mathrm{toBase} : X \to \operatorname{Spec} A$ be integral, proper, flat and locally of finite presentation, with $\varphi : F \cong$ the function field of $X$ carrying $A$ to the germ at the generic point of the structure map. Descent data are given: a discrete valuation ring $A_0$ with uniformiser $\varpi_0$, an injective local homomorphism $\iota_0 : A_0 \to A$ with every element of $A$ algebraic over its image, a model $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ with the same four properties, and an isomorphism $X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ over $\operatorname{Spec} A$. Point data are given: a point $x$ of $X$ above the closed point whose only specialisation is itself, two distinct generisations $\eta_1 \neq \eta_2$ of $x$ different from $x$ exhausting the generisations of $x$ lying above the closed point, and regular prolongations $R_1, R_2$ of $A$ in $F$ (valuation subrings of $F$ with surjective residue maps onto extensions $\bar F_i$ of the residue field of $A$, kernel the maximal ideal, compatible with $A$, and satisfying the normalisation condition) whose valuation subrings are the local rings of $X$ at $\eta_1, \eta_2$ transported through $\varphi$. Crossing data are given: $x_0$ the image of $x$ in $X_0$, an integer $w \geq 1$, and a ring isomorphism $e$ from the adic completion of $\mathcal O_{X_0,x_0}$ at its maximal ideal onto $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2, \hat A_0)/(X_0X_1 - \varpi_0^{w})$, carrying the image of $A_0$ to the constants. Finally a level is given: a discrete valuation ring $A_1$ with uniformiser $\varpi_1$, local homomorphisms $\iota_1' : A_0 \to A_1$ and $\iota_1 : A_1 \to A$ with $\iota_1$ injective and $\iota_1 \circ \iota_1' = \iota_0$, a pullback square exhibiting $f_1 : X_1 \to \operatorname{Spec} A_1$, $g_1 : X_1 \to X_0$ as the base change of $\mathrm{toBase}_0$ along $\operatorname{Spec} \iota_1'$, and an isomorphism $e_1 : X \cong X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$ compatible with $\mathrm{toBase}$ and with the projection to $X_0$. Write $\pi$ for $e_1.\mathrm{hom}$ followed by the first projection, a morphism $X \to X_1$. The conclusion is threefold: $g_1(\pi(x)) = x_0$; $\pi$ is flat; and every prime ideal $\mathfrak q$ of $\mathcal O_{X_1,\pi(x)}$ other than the maximal ideal is the preimage of the maximal ideal of $\mathcal O_{X,y}$ for some generisation $y \rightsquigarrow x$ with $y \neq x$, along the stalk map of $\pi$ at $x$ followed by the specialisation map $\mathcal O_{X,x} \to \mathcal O_{X,y}$.
--
--   This is the flatness half of the analysis of a node on a proper flat model after descending the base from the valuation ring $A$ to a discrete-valuation level $A_1$: it identifies the image of the node at the level and describes all non-maximal primes of the level stalk as centres of proper generisations. It feeds the determination of the completed local ring at the level point in [`AlgebraicCurve.stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk`](thm.html#AlgebraicCurve.stalk_level_of_isPullback_of_ringEquiv_adicCompletion_stalk).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.flat_fst_and_forall_isPrime_eq_comap_maximalIdeal_of_isPullback_of_ringEquiv_adicCompletion_stalk
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (η₁ η₂ : X) (h₁ : η₁ ⤳ x) (h₂ : η₂ ⤳ x) (h₁x : η₁ ≠ x) (h₂x : η₂ ≠ x) (h₁₂ : η₁ ≠ η₂)
    (hη : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = η₁ ∨ η = η₂)
    {Fbar₁ : Type} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hR₁ : R₁.integers.toSubring = SemistableModel.localRing X φ η₁)
    (hR₂ : R₂.integers.toSubring = SemistableModel.localRing X φ η₂)

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

    (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    (ι₁' : A₀ →+* A₁) [IsLocalHom ι₁'] (ι₁ : A₁ →+* ↥A) [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁)
    (hcomp : ι₁.comp ι₁' = ι₀)
    (ϖ₁ : A₁) (hϖ₁ : maximalIdeal A₁ = Ideal.span {ϖ₁})
    (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (g₁ : X₁ ⟶ X₀)
    (hsq : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι₁')))
    (e₁ : X ≅ Limits.pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ Limits.pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase)
    (he₁' : (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ g₁ =
      iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    :

    g₁.base ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) = x₀ ∧

    Flat (e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ∧
    (∀ 𝔮 : Ideal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)),
      𝔮.IsPrime → 𝔮 ≠ maximalIdeal (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) →
        ∃ (y : X) (hy : y ⤳ x), y ≠ x ∧
          𝔮 = (maximalIdeal (X.presheaf.stalk y)).comap
            ((X.presheaf.stalkSpecializes hy).hom.comp
              ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap x).hom)) := by sorry
