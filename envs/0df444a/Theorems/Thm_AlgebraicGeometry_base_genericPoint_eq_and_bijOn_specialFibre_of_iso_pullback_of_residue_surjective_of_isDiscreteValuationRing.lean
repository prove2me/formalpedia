-- Prove2me | Theorems.Thm_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0fd77a84-59e7-598c-9665-da29353b03d6
-- title:
--   Base change to a rank-one valuation ring: special fibre
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring such that (i) for all $a, b \in A$ with $a$ in the maximal ideal of $A$ and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$, and (ii) $A \neq L$ as subsets of $L$. Let $A_0$ be a discrete valuation ring (a domain) and $\iota : A_0 \to A$ an injective local ring homomorphism such that the composite of $\iota$ with the residue map of $A$ is surjective onto the residue field of $A$, and such that every element of $A$ is algebraic over the subring $\iota(A_0)$. Let $X_0$ be an integral scheme with a morphism $f_0 : X_0 \to \operatorname{Spec} A_0$ that is proper, flat and locally of finite presentation, all of whose local rings $\mathcal{O}_{X_0,y}$ are integrally closed, and assume: the structure map $A_0 \to \Gamma(X_0, \mathcal{O}_{X_0})$ induced by $f_0$ (through the canonical identification $\Gamma(\operatorname{Spec} A_0,\mathcal{O}) \cong A_0$) is bijective; every point of $X_0$ lying over the generic point $(0)$ of $\operatorname{Spec} A_0$ lies in the smooth locus of $f_0$; and every point $\eta_0$ lying over the closed point of $\operatorname{Spec} A_0$ which lies in the closure of some point $y \neq \eta_0$ lies in the smooth locus of $f_0$. Let $X$ be a scheme with a morphism $f : X \to \operatorname{Spec} A$ together with an isomorphism $X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ identifying $f$ with the second projection, and assume $X$ is integral. Writing $\mathrm{pr} : X \to X_0$ for the first projection (composed with the isomorphism), the conclusion asserts: $\mathrm{pr}$ sends the generic point of $X$ to the generic point of $X_0$; a point $x \in X$ lies over the closed point of $\operatorname{Spec} A$ if and only if $\mathrm{pr}(x)$ lies over the closed point of $\operatorname{Spec} A_0$; $\mathrm{pr}$ is injective on the set of points lying over the closed point of $\operatorname{Spec} A$; every point of $X_0$ over the closed point of $\operatorname{Spec} A_0$ is of the form $\mathrm{pr}(x)$; and for $x, y \in X$ both lying over the closed point of $\operatorname{Spec} A$ one has $x \rightsquigarrow y$ if and only if $\mathrm{pr}(x) \rightsquigarrow \mathrm{pr}(y)$, where $x \rightsquigarrow y$ means that $x$ lies in the closure of $\{y\}$.
--
--   This is the topological half of the base-change comparison between a proper flat normal model over a discrete valuation ring and its pullback to a rank-one valuation ring with the same residue field: the generic point is preserved and the special fibres correspond bijectively as partially ordered sets under specialisation. It is used in the construction and analysis of models of curves over valuation rings, in particular by the results identifying the stalks of the pullback along the smooth locus as valuation subrings and establishing integrality of the pullback in the relative dimension one case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
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
    [hX : IsIntegral X] :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    pr.base (genericPoint X) = genericPoint X₀ ∧
      (∀ x : X, toBase.base x = closedPoint ↥A ↔ toBase₀.base (pr.base x) = closedPoint A₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → pr.base x = pr.base y → x = y) ∧
      (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → ∃ x : X, pr.base x = x₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → (x ⤳ y ↔ pr.base x ⤳ pr.base y)) := by sorry
