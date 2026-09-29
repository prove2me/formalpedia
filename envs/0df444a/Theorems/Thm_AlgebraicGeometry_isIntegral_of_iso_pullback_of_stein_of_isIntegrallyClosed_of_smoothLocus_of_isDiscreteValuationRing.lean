-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/5e96dbdc-7d15-519b-aabe-a0b145039e6c
-- title:
--   Integrality of the base change of a normal Stein model
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring satisfying: for all $a,b \in A$ with $a$ in the maximal ideal of $A$ and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$ (a rank-one condition), and $A \neq L$ as subsets of $L$. Let $A_0$ be a domain which is a discrete valuation ring, and $\iota : A_0 \to A$ an injective local ring homomorphism such that the composite of $\iota$ with the residue map of $A$ is surjective and every element of $A$ is algebraic over the subring $\iota(A_0)$. Let $X_0$ be an integral scheme with a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ that is proper, flat and locally of finite presentation, such that every local ring of $X_0$ is integrally closed, the induced map $A_0 \to \Gamma(X_0, \mathcal{O}_{X_0})$ is bijective (the Stein condition), every point of $X_0$ lying over the generic point $(0)$ of $\operatorname{Spec} A_0$ lies in the smooth locus of $\mathrm{toBase}_0$, and every point $\eta_0$ lying over the closed point of $\operatorname{Spec} A_0$ which specialises to some point $y \neq \eta_0$ also lies in that smooth locus. Finally let $X$ carry a morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$ together with an isomorphism $X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ whose composite with the second projection is $\mathrm{toBase}$. Then $X$ is an integral scheme.
--
--   This is the integrality clause in the construction of a model over a rank-one valuation ring by base change from a normal Stein model over a discrete valuation subring; the Stein hypothesis is what forces the generic fibre to stay connected after arbitrary base field extension. It feeds the statement [`AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne`](thm.html#AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne), where the same model is analysed on its special fibre as well.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing
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
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase) :
    IsIntegral X := by sorry
