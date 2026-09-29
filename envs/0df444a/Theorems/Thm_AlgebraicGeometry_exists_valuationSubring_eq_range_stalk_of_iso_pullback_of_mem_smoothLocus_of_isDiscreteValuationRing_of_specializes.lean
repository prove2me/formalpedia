-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes
-- name    : AlgebraicGeometry.exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/bd3be288-f741-575a-bcbd-00dd6cb4c6c5
-- title:
--   Stalks at special generic points after base change to A
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring which is proper ($A \neq L$ as a set) and satisfies the rank-one condition that for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ one has $b \mid a^{n}$ for some $n \in \mathbb{N}$. Let $A_0$ be a discrete valuation ring (a domain) and $\iota : A_0 \to A$ an injective local ring homomorphism such that $A_0 \to A \to A/\mathfrak{m}_A$ is surjective and every element of $A$ is algebraic over the subring $\iota(A_0)$. Let $X_0$ be an integral scheme with a proper, flat, locally of finite presentation morphism $f_0 : X_0 \to \operatorname{Spec} A_0$ such that all stalks of $X_0$ are integrally closed; assume the Stein condition that $a \mapsto f_0^{\sharp}(a)$ is a bijection from $A_0$ onto $\Gamma(X_0,\mathcal{O}_{X_0})$, that every point over the generic point of $\operatorname{Spec} A_0$ lies in the smooth locus of $f_0$, that every non-closed point of $X_0$ lying over the closed point of $\operatorname{Spec} A_0$ lies in the smooth locus of $f_0$, and the relative dimension one condition that if $\eta$ is such a non-closed special point and $\eta \rightsquigarrow y$ with $y \neq \eta$, then $y$ is a closed point. Let $X$ be an integral scheme with $g : X \to \operatorname{Spec} A$ together with an isomorphism $X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ carrying $g$ to the second projection, and write $\mathrm{pr} : X \to X_0$ for the composite of this isomorphism with the first projection. Then for every point $\eta$ of $X$ lying over the closed point of $\operatorname{Spec} A$ and admitting a specialisation $y \neq \eta$, there is a valuation subring $O$ of the function field $K(X)$ whose underlying subring is the image of $\mathcal{O}_{X,\eta} \to K(X)$, and such that, granted that $\mathrm{pr}$ sends the generic point of $X$ to the generic point of $X_0$, for every $g \in K(X_0)$ the image of $g$ under the induced map $K(X_0) \to K(X)$ (the stalk specialisation isomorphism at the generic point of $X_0$ followed by the stalk map of $\mathrm{pr}$) lies in $O$ if and only if $g$ lies in the image of $\mathcal{O}_{X_0,\mathrm{pr}(\eta)} \to K(X_0)$.
--
--   This is the base-change step for models of relative dimension one: it transports the local structure at a generic point of the special fibre from a proper flat model over a discrete valuation ring to its base change along a local injective map into a rank-one valuation subring with trivial residue extension and algebraic generic fibre, identifying the image of the stalk in $K(X)$ as a valuation ring of $K(X)$ that traces back exactly to the corresponding stalk of $X_0$ inside $K(X_0)$. It feeds into [`AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne`](thm.html#AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne), and draws on the pullback preservation of properness, flatness and finite presentation, the bijection between the generic points of the two special fibres, and the discreteness of the stalks at smooth non-closed special points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_valuationSubring_eq_range_stalk_of_iso_pullback_of_mem_smoothLocus_of_isDiscreteValuationRing_of_specializes
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)

    (hdim₀ : ∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X₀, y ⤳ z → z = y)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [hX : IsIntegral X] :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    ∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
      ∃ O : ValuationSubring X.functionField,
        O.toSubring = (algebraMap (X.presheaf.stalk η) X.functionField).range ∧
        ∀ (hgen : pr.base (genericPoint X) = genericPoint X₀) (g : X₀.functionField),
          (pr.stalkMap (genericPoint X)).hom
              ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g) ∈ O ↔
            g ∈ (algebraMap (X₀.presheaf.stalk (pr.base η)) X₀.functionField).range := by sorry
