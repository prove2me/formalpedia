-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian
-- name    : AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/e0f088c1-0484-517c-b202-63711f00d2a8
-- title:
--   Normal proper model with prescribed geometric valuations
-- statement:
--   Let $A_0$ be a henselian discrete valuation ring (a domain), with $\varpi_0$ generating its maximal ideal; let $L$ be a field of characteristic zero, $\iota_0 : A_0 \to L$ an injective ring homomorphism, and $K_0 \subseteq L$ a subfield containing $\iota_0(A_0)$ each of whose elements $x$ satisfies $x\,\iota_0(b) = \iota_0(a)$ for some $a, b \in A_0$ with $b \neq 0$ (so $K_0$ is the fraction field of $\iota_0(A_0)$ in $L$), and assume every element of $L$ is algebraic over $K_0$. Let $F$ be a field extension of $L$ which is a curve over $L$ in the project's sense (every nonzero element has a principal divisor of degree zero, every place of $F/L$ has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$, with $L$ algebraically closed in $F$ (every $x \in F$ algebraic over $L$ lies in the image of $L$). Let $F_0 \subseteq F$ be a subfield with $F_0 \cap L = K_0$ (i.e. $\mathrm{alg}_L(c) \in F_0 \iff c \in K_0$) which $L$-spans $F$: every $f \in F$ is a quotient $\bigl(\sum_i c_i g_i\bigr) / \bigl(\sum_i d_i g_i'\bigr)$ of two finite $L$-linear combinations of elements of $F_0$, the denominator nonzero. Let $j_0 : A_0 \to F_0$ be a ring homomorphism inducing $\iota_0$ on $L \subseteq F$, and let $V$ be a nonempty finite set of valuation subrings of $F_0$ such that each $O \in V$ contains $j_0(A_0)$ with $j_0(\varpi_0)$ in the maximal ideal of $O$, and is geometric in the sense that there is $f \in O$ for which, for every polynomial $p$ over $A_0$ having at least one unit coefficient, $p^{j_0}(f)$ lies in $O$ and is a unit of $O$. The conclusion asserts the existence of a scheme $X_0$, a morphism $\pi : X_0 \to \operatorname{Spec} A_0$ which is proper, flat and locally of finite presentation with $X_0$ integral, and a ring isomorphism $\varphi_0 : F_0 \xrightarrow{\sim} K(X_0)$ onto the function field, such that: $\varphi_0 \circ j_0$ is the canonical map $A_0 \to \Gamma(X_0) \to K(X_0)$; every stalk of $X_0$ is integrally closed; $a \mapsto \pi^{\sharp}(a)$ is a bijection $A_0 \to \Gamma(X_0)$; every point lying over the generic point of $\operatorname{Spec} A_0$ lies in the smooth locus of $\pi$; every proper specialisation of a non-closed point of the special fibre is closed; every valuation subring $O' \neq \top$ of $F_0$ containing $(j_0 a)^{-1}$ for all $a \neq 0$ is the image in $F_0$ under $\varphi_0^{-1}$ of the stalk at some point of $X_0$; and the non-closed points of $X_0$ lying over the closed point of $\operatorname{Spec} A_0$ have local rings, transported to $F_0$ by $\varphi_0^{-1}$, exactly the members of $V$, each member being attained.
--
--   This is the construction of a normal proper flat model over a henselian discrete valuation ring of a one-variable function field given as a $K_0$-form $F_0$ of $F/L$, whose special-fibre components correspond exactly to a prescribed finite set of residually transcendental valuations, with Stein global sections, smooth generic fibre and a complete generic-fibre model. It is used in the construction of semistable models of modular curves of full level over the descent base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    {L : Type} [Field L] [CharZero L] (ι₀ : A₀ →+* L) (hι₀ : Function.Injective ι₀)
    (K₀ : Subfield L) (hK₀A : ∀ a : A₀, ι₀ a ∈ K₀)
    (hK₀ : ∀ x : L, x ∈ K₀ → ∃ a b : A₀, b ≠ 0 ∧ x * ι₀ b = ι₀ a)

    (hLK₀ : ∀ x : L, IsAlgebraic ↥K₀ x)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
    (F₀ : Subfield F)
    (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → ↥F₀) (d : Fin n → L) (g' : Fin n → ↥F₀),
      (∑ i, d i • (g' i : F)) ≠ 0 ∧ f * (∑ i, d i • (g' i : F)) = ∑ i, c i • (g i : F))

    (j₀ : A₀ →+* ↥F₀) (hj₀ : ∀ a : A₀, ((j₀ a : ↥F₀) : F) = algebraMap L F (ι₀ a))
    (V : Finset (ValuationSubring ↥F₀)) (hV : V.Nonempty)
    (hdom : ∀ O ∈ V, (∀ a : A₀, j₀ a ∈ O) ∧ ∃ hO : j₀ ϖ₀ ∈ O, (⟨_, hO⟩ : ↥O) ∈ maximalIdeal ↥O)
    (hgeo : ∀ O ∈ V, ∃ f : ↥F₀, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    ∃ (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
      (_ : IsIntegral X₀) (_ : IsProper toBase₀) (_ : Flat toBase₀) (_ : LocallyOfFinitePresentation toBase₀)
      (φ₀ : ↥F₀ ≃+* X₀.functionField),
      (∀ a : A₀, φ₀ (j₀ a) = SemistableModel.baseToFunctionField toBase₀ a) ∧
      (∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y)) ∧
      Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)) ∧
      (∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus) ∧

      (∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
        ∀ z : X₀, y ⤳ z → z = y) ∧

      (∀ O' : ValuationSubring ↥F₀, O' ≠ ⊤ → (∀ a : A₀, a ≠ 0 → (j₀ a : ↥F₀)⁻¹ ∈ O') →
        ∃ y : X₀, O'.toSubring = SemistableModel.localRing X₀ φ₀ y) ∧
      (∀ O ∈ V, ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
        SemistableModel.localRing X₀ φ₀ η = O.toSubring) ∧
      (∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
        ∃ O ∈ V, SemistableModel.localRing X₀ φ₀ η = O.toSubring) := by sorry
