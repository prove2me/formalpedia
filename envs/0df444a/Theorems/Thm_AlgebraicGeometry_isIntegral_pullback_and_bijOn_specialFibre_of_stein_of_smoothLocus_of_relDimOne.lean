-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne
-- name    : AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/aa61f6ac-423e-56ef-a8f4-4f5f60f6a427
-- title:
--   Base change of a normal Stein model along A₀ → A
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring satisfying: for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$, and $A \neq L$ as a subset. Let $A_0$ be a discrete valuation ring (a domain) and $\iota : A_0 \to A$ an injective local ring homomorphism such that the composite of $\iota$ with the residue map of $A$ is surjective and every element of $A$ is algebraic over the subring $\iota(A_0)$. Let $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ be proper, flat and locally of finite presentation with $X_0$ integral, all stalks of $X_0$ integrally closed, the map $A_0 \to \Gamma(X_0, \mathcal{O})$ induced by $\mathrm{toBase}_0$ bijective, every point lying over the zero ideal in the smooth locus of $\mathrm{toBase}_0$, every point $\eta_0$ over the closed point of $\operatorname{Spec} A_0$ which specialises to some $y \neq \eta_0$ in the smooth locus of $\mathrm{toBase}_0$, and the condition $\mathrm{hdim}_0$: for $\eta$ over the closed point with $\eta \rightsquigarrow z$ for some $z \neq \eta$, any $y \neq \eta$ with $\eta \rightsquigarrow y$ is closed in the specialisation order ($y \rightsquigarrow z$ implies $z = y$). Let $\mathrm{toBase} : X \to \operatorname{Spec} A$ together with an isomorphism $\mathrm{iso}$ of $X$ with the pullback of $\mathrm{toBase}_0$ along $\operatorname{Spec}(\iota)$ be given, such that $\mathrm{iso}$ followed by the second projection is $\mathrm{toBase}$, and set $pr$ to be $\mathrm{iso}$ followed by the first projection. Then $X$ is integral, $\mathrm{toBase}$ is proper, flat and locally of finite presentation, and: $pr$ sends the generic point of $X$ to that of $X_0$; a point $x$ lies over the closed point of $\operatorname{Spec} A$ iff $pr(x)$ lies over the closed point of $\operatorname{Spec} A_0$; $pr$ is injective on points over the closed point and hits every point of $X_0$ over the closed point of $\operatorname{Spec} A_0$; among such points $pr$ both preserves and reflects specialisation; $x$ lies in the smooth locus of $\mathrm{toBase}$ iff $pr(x)$ lies in the smooth locus of $\mathrm{toBase}_0$; the analogue of $\mathrm{hdim}_0$ holds for $X$; and for each non-closed point $\eta$ over the closed point of $\operatorname{Spec} A$ there is a valuation subring $O$ of the function field of $X$ whose underlying subring is the image of the stalk at $\eta$ in that function field, and such that for every proof that $pr$ maps generic point to generic point and every $g$ in the function field of $X_0$, the image of $g$ under the stalk specialisation map followed by the stalk map of $pr$ at the generic point lies in $O$ iff $g$ lies in the image of the stalk of $X_0$ at $pr(\eta)$.
--
--   This is the base-change step for semistable models: a normal, proper, flat model over a discrete valuation ring with Stein global sections, smooth generic fibre and one-dimensional special fibre is transported to the rank-one valuation ring $A$, with the special fibre, its specialisation order, the smooth locus and the local rings at non-closed special points all read off on the original model. It is used in the construction of semistable descent data for modular curves and in the verification that the pulled-back scheme again has integrally closed stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_pullback_and_bijOn_specialFibre_of_stein_of_smoothLocus_of_relDimOne
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
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase) :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    ∃ (_ : IsIntegral X) (_ : IsProper toBase) (_ : Flat toBase) (_ : LocallyOfFinitePresentation toBase),

      pr.base (genericPoint X) = genericPoint X₀ ∧
      (∀ x : X, toBase.base x = closedPoint ↥A ↔ toBase₀.base (pr.base x) = closedPoint A₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → pr.base x = pr.base y → x = y) ∧
      (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → ∃ x : X, pr.base x = x₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → (x ⤳ y ↔ pr.base x ⤳ pr.base y)) ∧

      (∀ x : X, x ∈ toBase.smoothLocus ↔ pr.base x ∈ toBase₀.smoothLocus) ∧

      (∀ η y : X, toBase.base η = closedPoint ↥A → (∃ z : X, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
        ∀ z : X, y ⤳ z → z = y) ∧

      (∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
        ∃ O : ValuationSubring X.functionField,
          O.toSubring = (algebraMap (X.presheaf.stalk η) X.functionField).range ∧
          ∀ (hgen : pr.base (genericPoint X) = genericPoint X₀) (g : X₀.functionField),
            (pr.stalkMap (genericPoint X)).hom
                ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g) ∈ O ↔
              g ∈ (algebraMap (X₀.presheaf.stalk (pr.base η)) X₀.functionField).range) := by sorry
