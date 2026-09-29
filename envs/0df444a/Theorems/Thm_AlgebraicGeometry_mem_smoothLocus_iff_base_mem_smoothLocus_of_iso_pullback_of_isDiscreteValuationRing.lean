-- Prove2me | Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/6fe19787-5f00-5111-8172-740b627c80ae
-- title:
--   Smoothness after base change to a rank-one valuation ring
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring satisfying two conditions: for all $a,b \in A$ with $a$ in the maximal ideal of $A$ and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$ (a rank-one condition), and $A \neq L$ as subsets of $L$ (the valuation is nontrivial). Let $A_{0}$ be a discrete valuation ring (a domain with `IsDiscreteValuationRing`) and $\iota : A_{0} \to A$ an injective local ring homomorphism such that the composite $A_{0} \to A \to A/\mathfrak{m}_{A}$ is surjective, and such that every element of $A$ is algebraic over the image subring $\iota(A_{0})$. Let $X_{0}$ be a scheme with a morphism $\mathrm{toBase}_{0} : X_{0} \to \operatorname{Spec} A_{0}$ which is proper, flat and locally of finite presentation, with $X_{0}$ integral and all local rings $\mathcal{O}_{X_{0},y}$ integrally closed; assume further that the structural map $A_{0} \to \Gamma(X_{0},\mathcal{O}_{X_{0}})$ obtained from $\mathrm{toBase}_{0}$ and the canonical identification of $A_{0}$ with the global sections of $\operatorname{Spec} A_{0}$ is bijective, that every point of $X_{0}$ lying over the generic point $\bot$ of $\operatorname{Spec} A_{0}$ lies in the smooth locus of $\mathrm{toBase}_{0}$, and that every point $\eta_{0}$ lying over the closed point of $\operatorname{Spec} A_{0}$ which specialises to some point distinct from itself (i.e. is not closed) also lies in that smooth locus. Finally let $X$ be a scheme with $\mathrm{toBase} : X \to \operatorname{Spec} A$ locally of finite presentation, together with an isomorphism $\mathrm{iso}$ from $X$ to the fibre product of $\mathrm{toBase}_{0}$ and $\operatorname{Spec}(\iota)$ such that $\mathrm{iso}$ followed by the second projection is $\mathrm{toBase}$. Writing $\mathrm{pr}$ for $\mathrm{iso}$ followed by the first projection, the conclusion is that for every point $x$ of $X$ one has $x \in \operatorname{Sm}(\mathrm{toBase})$ if and only if $\mathrm{pr}(x) \in \operatorname{Sm}(\mathrm{toBase}_{0})$.
--
--   This is the statement that the smooth locus of a model over a rank-one valuation ring obtained by base change along $A_{0} \to A$ is exactly the preimage of the smooth locus of the model over the discrete valuation ring, the two directions being base change of smoothness and descent along the flat map $\operatorname{Spec} A \to \operatorname{Spec} A_{0}$. It is used in the construction of semistable models, being cited by [`AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne`](thm.html#AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne); the proof identifies stalks via [`AlgebraicGeometry.exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective`](thm.html#AlgebraicGeometry.exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective) and reads smoothness off formal smoothness of the stalk through [`AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk`](thm.html#AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing
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
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [hlfp : LocallyOfFinitePresentation toBase] :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    ∀ x : X, x ∈ toBase.smoothLocus ↔ pr.base x ∈ toBase₀.smoothLocus := by sorry
