-- Prove2me | Theorems.Thm_AlgebraicCurve_isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
-- name    : AlgebraicCurve.isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/39c78804-6ed6-5c58-b140-c8afd8829676
-- title:
--   Node stalk over a discrete-valuation level: noetherian, dimension ≥ 2
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring such that for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$. Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$. Let $A_0$ be a discrete valuation domain, $\iota_0 : A_0 \to A$ an injective local homomorphism, $\varpi_0$ a generator of the maximal ideal of $A_0$, and assume every element of $A$ is algebraic over the image of $\iota_0$; let $X_0$ be integral with $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ proper, flat and locally of finite presentation, together with an isomorphism $\mathrm{iso} : X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ over $\operatorname{Spec} A$. Let $x \in X$ lie over the closed point of $A$, be closed (any $y$ with $x \rightsquigarrow y$ equals $x$), and admit a generisation $\eta \rightsquigarrow x$, $\eta \neq x$, also lying over the closed point; let $x_0$ be the image of $x$ in $X_0$. Assume $w \ge 1$ and a ring isomorphism $e$ from the $\mathfrak m$-adic completion of $\mathcal O_{X_0,x_0}$ onto $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2, \hat A_0)/(X_0X_1 - C(\varpi_0^{w}))$, where $\hat A_0$ is the completion of $A_0$, carrying the germ of each $a \in A_0$ pulled back along $\mathrm{toBase}_0$ to the class of the constant series $C(a)$. Finally let $A_1$ be a discrete valuation domain with local maps $\iota_1' : A_0 \to A_1$ and an injective local $\iota_1 : A_1 \to A$ satisfying $\iota_1 \circ \iota_1' = \iota_0$, with uniformiser $\varpi_1$, and let $f_1 : X_1 \to \operatorname{Spec} A_1$, $g_1 : X_1 \to X_0$ be a pullback square over $\operatorname{Spec}(\iota_1')$, together with an isomorphism $e_1 : X \cong X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$ compatible with $\mathrm{toBase}$ and with the projections to $X_0$. Writing $x_1$ for the image of $x$ in $X_1$, the conclusion is that $\mathcal O_{X_1,x_1}$ is noetherian, that its Krull dimension is at least $2$, and that there exist $e' \in \mathbb N$ and a unit $v$ of $\mathcal O_{X_1,x_1}$ with the germ at $x_1$ of $\iota_1'(\varpi_0)$, pulled back along $f_1$, equal to $v$ times the $e'$-th power of the germ of $\varpi_1$.
--
--   This records the local structure at a node of a semistable model after base change to an intermediate discrete-valuation level: the stalk of the level model at the node is noetherian of dimension at least two, and the lower uniformiser becomes a unit times a power of the level uniformiser. It feeds the normality statement [`AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ringEquiv_adicCompletion_stalk_of_isDiscreteValuationRing) and the node analysis built on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.isNoetherianRing_stalk_and_two_le_ringKrullDim_and_exists_eq_mul_pow_of_isPullback_of_ringEquiv_adicCompletion_stalk_min
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
    (hbranch : ∃ η : X, η ⤳ x ∧ η ≠ x ∧ toBase.base η = closedPoint ↥A)

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
    IsNoetherianRing (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) ∧
    2 ≤ ringKrullDim (X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) ∧
    (∃ (e' : ℕ) (v : X₁.presheaf.stalk ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)),
      IsUnit v ∧
      (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (ι₁' ϖ₀))) =
        v * (X₁.presheaf.germ ⊤ ((e₁.hom ≫ Limits.pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x) trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁)) ^ e') := by sorry
