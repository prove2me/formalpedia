-- Prove2me | Theorems.Thm_AlgebraicCurve_ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne
-- name    : AlgebraicCurve.ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/0050d111-e675-524a-bd4c-46311780762c
-- title:
--   Distinct non-maximal branch kernels on a descended node ring
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring satisfying the condition that for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$. Let $F$ be a field over $L$ which is a curve over $L$ in the sense of the project predicate (every nonzero element has a degree-zero divisor computing its orders at all places, every place has residue field finite over $L$, and $\Omega[F/L]$ is free of rank one), and essentially of finite type over $L$. Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$, and $\varphi : F \cong \mathrm{FF}(X)$ a ring isomorphism carrying $\mathrm{algebraMap}\,L\,F(a)$, for $a \in A$, to the image of $a$ under the germ at the generic point of the structure map on global sections. Let $A_0$ be a henselian discrete valuation domain, $\iota_0 : A_0 \to A$ an injective local homomorphism whose composite with the residue map of $A$ is surjective (so the residue fields agree), $\varpi_0$ a generator of the maximal ideal of $A_0$, and suppose every element of $A$ is algebraic over the image subring $\iota_0.\mathrm{range}$. Let $X_0$ be integral with $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ proper, flat and locally of finite presentation, together with an isomorphism $\mathrm{iso} : X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ whose composite with the second projection is $\mathrm{toBase}$. Let $x \in X$ lie over the closed point of $A$ and be closed (any $y$ with $x \rightsquigarrow y$ equals $x$), and let $\eta_1 \neq \eta_2$ be points, both distinct from $x$, specialising to $x$, such that every point specialising to $x$, distinct from $x$ and lying over the closed point of $A$ is $\eta_1$ or $\eta_2$. Let $\bar F_1, \bar F_2$ be fields over the residue field of $A$ and $R_1, R_2$ regular prolongations of $A$ in $F$ with values in them — that is, valuation subrings $R_i.\mathrm{integers}$ of $F$ meeting $L$ exactly in $A$, equipped with surjective homomorphisms $R_i.\mathrm{residue}$ to $\bar F_i$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero $f \in F$ has an $L$-multiple lying in $R_i.\mathrm{integers}$ with nonzero residue — whose underlying subrings are the local rings $\varphi^{-1}(\mathcal O_{X,\eta_i})$ of $X$ at $\eta_1$, $\eta_2$. Let $x_0 \in X_0$ be the image of $x$ under $\mathrm{iso}$ followed by the first projection, let $w \geq 1$ be a natural number invertible in $A_0$, and let $e$ be a ring isomorphism from the adic completion of $\mathcal O_{X_0,x_0}$ at its maximal ideal onto the crossing model $W[[u,v]]/(uv - \varpi_0^{w})$, where $W$ is the adic completion of $A_0$, such that $e$ sends the image of each $a \in A_0$ (through the structure map, the germ at $x_0$ and the completion) to the constant class of $a$. Finally let $\mathcal N_0 \subseteq F$ be a local subring consisting exactly of those $f$ with $\varphi f$ in the image of $\mathcal O_{X_0,x_0}$ under the stalk map of $\mathrm{iso}$ followed by the first projection, composed with the map to the function field, and assume $\mathcal N_0$ is contained in $\varphi^{-1}(\mathcal O_{X,x})$ and in both $R_i.\mathrm{integers}$. Then the kernels of $R_1.\mathrm{residue}$ and $R_2.\mathrm{residue}$ restricted along the inclusions of $\mathcal N_0$ are distinct from each other and each distinct from the maximal ideal of $\mathcal N_0$.
--
--   This is the separation statement for the two branches through an ordinary double point of a proper flat model, after descent to a henselian discrete valuation ring with the same residue field: the two branch reductions cut out two distinct primes of the descended local ring at the node, neither of them the maximal ideal. It feeds the construction of node coordinates and the uniqueness of the branch assignment used in the analysis of the special fibre of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (hres₀ : Function.Surjective ((IsLocalRing.residue ↥A).comp ι₀))
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
    (w : ℕ) (hw : 1 ≤ w) (hwu : IsUnit ((w : ℕ) : A₀))
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))

    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀]
    (hmem₀ : ∀ f : F, f ∈ 𝒩₀ ↔ ∃ g : X₀.presheaf.stalk ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x),
      φ f = algebraMap (X.presheaf.stalk x) X.functionField
        (((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).stalkMap x).hom g))
    (hle : 𝒩₀ ≤ SemistableModel.localRing X φ x)
    (hle₁ : 𝒩₀ ≤ R₁.integers.toSubring) (hle₂ : 𝒩₀ ≤ R₂.integers.toSubring) :
    RingHom.ker (R₁.residue.comp (Subring.inclusion hle₁)) ≠ RingHom.ker (R₂.residue.comp (Subring.inclusion hle₂)) ∧
    RingHom.ker (R₁.residue.comp (Subring.inclusion hle₁)) ≠ maximalIdeal ↥𝒩₀ ∧
    RingHom.ker (R₂.residue.comp (Subring.inclusion hle₂)) ≠ maximalIdeal ↥𝒩₀ := by sorry
