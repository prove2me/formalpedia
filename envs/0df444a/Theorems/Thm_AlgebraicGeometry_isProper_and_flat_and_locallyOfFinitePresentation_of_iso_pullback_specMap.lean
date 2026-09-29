-- Prove2me | Theorems.Thm_AlgebraicGeometry_isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap
-- name    : AlgebraicGeometry.isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/ef11220d-4ddd-5017-9c6a-29a007004f9f
-- title:
--   Properness, flatness and finite presentation under base change
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, subject to two conditions: for all $a, b \in A$ with $a$ in the maximal ideal of $A$ and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$, and $A$ is not the whole of $L$ as a subset. Let $A_0$ be a commutative domain which is a discrete valuation ring, and $\iota : A_0 \to A$ an injective local ring homomorphism such that the composite of $\iota$ with the residue map $A \to A/\mathfrak{m}_A$ is surjective and every element of $A$ is algebraic over the image subring $\iota(A_0)$. Let $X_0$ be an integral scheme (in universe $0$) with a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ that is proper, flat and locally of finite presentation, all of whose local rings are integrally closed, such that the induced map $A_0 \to \Gamma(X_0, \mathcal{O}_{X_0})$ (the global-sections map of $\mathrm{toBase}_0$ composed with the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism) is bijective, such that every point lying over the generic point $(0)$ of $\operatorname{Spec} A_0$ lies in the smooth locus of $\mathrm{toBase}_0$, and such that every point $\eta_0$ lying over the closed point of $\operatorname{Spec} A_0$ which specialises to some point distinct from itself lies in the smooth locus of $\mathrm{toBase}_0$. Let $X$ be a scheme with a morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$ and an isomorphism $\mathrm{iso} : X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ whose composite with the second projection is $\mathrm{toBase}$. Then $\mathrm{toBase}$ is proper, flat and locally of finite presentation. The proof uses none of the hypotheses on $A$ and $\iota$, nor the normality, Stein and smooth-locus hypotheses on $\mathrm{toBase}_0$.
--
--   This is the stability of properness, flatness and local finite presentation under base change, transported along a given identification of $X$ with the fibre product $X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$. Its long hypothesis list matches that of the surrounding results on semistable models over rank-one valuation rings, which cite it to equip the base-changed family with the three properties they need.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap
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
    IsProper toBase ∧ Flat toBase ∧ LocallyOfFinitePresentation toBase := by sorry
