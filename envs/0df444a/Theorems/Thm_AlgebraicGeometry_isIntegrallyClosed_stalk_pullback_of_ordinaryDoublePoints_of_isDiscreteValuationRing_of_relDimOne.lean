-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegrallyClosed_stalk_pullback_of_ordinaryDoublePoints_of_isDiscreteValuationRing_of_relDimOne
-- name    : AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ordinaryDoublePoints_of_isDiscreteValuationRing_of_relDimOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/a6d83120-e2e5-5a11-bbce-3dbdeb749c46
-- title:
--   Normality of the base change of a nodal curve
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring satisfying: for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$ (rank at most one), and $A \neq L$. Let $A_0$ be a discrete valuation ring with uniformiser $\varpi_0$ (so $\mathfrak m_{A_0} = (\varpi_0)$), and $\iota : A_0 \to A$ an injective local ring homomorphism such that $A_0 \to A \to A/\mathfrak m_A$ is surjective and every element of $A$ is algebraic over the subring $\iota(A_0)$. Let $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ be proper, flat and locally of finite presentation with $X_0$ integral, all stalks of $X_0$ integrally closed, and $A_0 \to \Gamma(X_0, \mathcal O_{X_0})$ (via $\mathrm{toBase}_0$ on global sections) bijective. Assume: every point over the generic point $(\bot)$ of $\operatorname{Spec} A_0$ lies in the smooth locus; every non-closed point $\eta_0$ over the closed point (one admitting $y \neq \eta_0$ with $\eta_0 \rightsquigarrow y$) lies in the smooth locus; relative dimension one, in the form that any $y \neq \eta$ specialising from such an $\eta$ is closed; and every point $x_0$ over the closed point outside the smooth locus has noetherian stalk whose $\mathfrak m$-adic completion is isomorphic, compatibly with the constants coming from $A_0$, to $\widehat{A_0}[[X_0, X_1]]/(X_0X_1 - \varpi_0^{w})$ for some $w \geq 1$. Finally let $\mathrm{toBase} : X \to \operatorname{Spec} A$ be a scheme over $A$ together with an isomorphism $X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ whose composite with the second projection is $\mathrm{toBase}$. Then every stalk of $X$ is integrally closed.
--
--   This is the statement that normality of a semistable curve over a discrete valuation ring, smooth away from ordinary double points on the special fibre, is inherited by its base change to a rank-one valuation ring with the same residue field and algebraic fraction-field extension. It supplies the normality clause in the construction of the semistable scheme model of the full-level modular curve, and is cited by the three [`ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich`](thm.html#ModularCurve.FullLevel.exists_semistableScheme_descent_of_valuationSubrings_and_smoothLocus_iff_of_isUnit_width_jDich) results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegrallyClosed_stalk_pullback_of_ordinaryDoublePoints_of_isDiscreteValuationRing_of_relDimOne.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegrallyClosed_stalk_pullback_of_ordinaryDoublePoints_of_isDiscreteValuationRing_of_relDimOne
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
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hnode₀ : ∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → x₀ ∉ toBase₀.smoothLocus →
      IsNoetherianRing (X₀.presheaf.stalk x₀) ∧
      ∃ (w : ℕ), 1 ≤ w ∧
        ∃ e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
            (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
                MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}),
          ∀ a : A₀,
            e (algebraMap (X₀.presheaf.stalk x₀) _
                ((X₀.presheaf.germ ⊤ x₀ trivial).hom (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
              Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a)))
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase) :
    ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) := by sorry
