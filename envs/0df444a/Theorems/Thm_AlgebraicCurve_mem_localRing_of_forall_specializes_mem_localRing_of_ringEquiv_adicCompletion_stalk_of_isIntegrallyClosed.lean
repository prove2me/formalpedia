-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
-- name    : AlgebraicCurve.mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/ff82590b-602e-59cc-a9e9-847d882d2a9a
-- title:
--   Local ring at a node: intersection over proper generisations
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring such that for all $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ one has $b\mid a^{n}$ for some $n$. Let $F/L$ be a field which is essentially of finite type over $L$ and a curve over $L$ in the sense of `IsCurveOver` (principal divisors exist, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$). Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism `toBase` to $\operatorname{Spec} A$, all of whose stalks are integrally closed, together with a ring isomorphism $\varphi\colon F\to$ the function field of $X$ carrying $\operatorname{algebraMap}_{L,F}(a)$ to the image of $a\in A$ under `SemistableModel.baseToFunctionField toBase`. Assume a descent datum: a discrete valuation ring $A_0$, an injective local homomorphism $\iota_0\colon A_0\to A$ with every element of $A$ algebraic over $\iota_0(A_0)$, a uniformiser $\varpi_0$ generating the maximal ideal of $A_0$, an integral scheme $X_0$ proper, flat and locally of finite presentation over $\operatorname{Spec} A_0$, and an isomorphism `iso` of $X$ with the pullback of `toBase₀` along $\operatorname{Spec}(\iota_0)$ compatible with the projections. Let $x\in X$ lie over the closed point of $A$, admit no proper specialisation, and have exactly two distinct proper generisations $\eta_1\neq\eta_2$ inside the closed fibre, in the sense that any generisation $\eta\neq x$ of $x$ lying over the closed point of $A$ equals $\eta_1$ or $\eta_2$; assume further that the subrings `SemistableModel.localRing X φ ηᵢ` of $F$ (the images in $F$, via $\varphi^{-1}$, of the stalks of $X$ at $\eta_i$ inside the function field) are the integers of regular prolongations $R_i$ of $A$ in $F$ with residue fields $\overline{F}_i$ over the residue field of $A$. Finally, with $x_0\in X_0$ the image of $x$ under `iso.hom` followed by the first projection, assume $w\geq 1$ and a ring isomorphism $e$ from the adic completion of the stalk of $X_0$ at $x_0$ along its maximal ideal onto the crossing model $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2,\widehat{A_0})/(X_0X_1-C(\varpi_0^{w}))$ over the adic completion $\widehat{A_0}$ of $A_0$, which sends the image of each $a\in A_0$ (taken through `toBase₀` on global sections, the germ at $x_0$, and the completion) to the class of the constant $a$. Then for every $f\in F$: if $f$ belongs to `SemistableModel.localRing X φ y` for every $y\neq x$ with $x$ a specialisation of $y$, then $f$ belongs to `SemistableModel.localRing X φ x`.
--
--   This is the Krull-type statement that, at a point $x$ of the closed fibre whose completed local ring is an $A_0$-crossing model, the local ring of $X$ at $x$, viewed inside $F$, is cut out by the local rings at the proper generisations of $x$; normality of $X$ and descent to the discrete-valuation-ring level are the inputs. It feeds the node package of the global construction of a semistable model, being cited by [`AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed`](thm.html#AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
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
    :
    ∀ f : F, (∀ y : X, y ⤳ x → y ≠ x → f ∈ SemistableModel.localRing X φ y) → f ∈ SemistableModel.localRing X φ x := by sorry
