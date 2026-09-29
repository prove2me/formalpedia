-- Prove2me | Theorems.Thm_AlgebraicCurve_localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing
-- name    : AlgebraicCurve.localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/9b5ff544-e31d-5292-9c3e-b2d5d9268e70
-- title:
--   Node local ring lies in both branches and all S-places
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring such that for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ one has $b \mid a^{n}$ for some $n$. Let $F$ be a field extension of $L$ that is a curve over $L$ in the project's sense (principal divisors exist, each place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$. Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism $\mathrm{toBase} : X \to \operatorname{Spec} A$, and $\varphi : F \cong K(X)$ a ring isomorphism carrying $\mathrm{algebraMap}\,L\,F(a)$, for $a \in A$, to the germ at the generic point of the global section of $\mathcal{O}_X$ determined by $a$ through $\mathrm{toBase}$. Assume further: a discrete valuation ring $A_0$ with an injective local homomorphism $\iota_0 : A_0 \to A$, a generator $\varpi_0$ of the maximal ideal of $A_0$, every element of $A$ algebraic over the image of $\iota_0$; an integral $X_0$ with $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ proper, flat and locally of finite presentation, together with an isomorphism $X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ whose composite with the second projection is $\mathrm{toBase}$; a point $x \in X$ over the closed point of $A$ which is maximal for specialisation (every $y$ with $x \rightsquigarrow y$ equals $x$); two distinct points $\eta_1 \neq \eta_2$, both distinct from $x$ and specialising to $x$, such that any point $\eta \neq x$ specialising to $x$ and lying over the closed point of $A$ is $\eta_1$ or $\eta_2$; fields $\bar F_1, \bar F_2$ over the residue field of $A$ and regular prolongations $R_1, R_2$ of $A$ to $F$ with values in them (valuation subrings of $F$ equipped with a surjective residue map onto $\bar F_i$ whose kernel is the maximal ideal, inducing $A$ on $L$ and compatible with the residue map of $A$) whose rings of integers are, as subrings of $F$, the rings $\varphi^{-1}(\mathcal{O}_{X,\eta_1})$ and $\varphi^{-1}(\mathcal{O}_{X,\eta_2})$; the image $x_0$ of $x$ under the first projection; an integer $w \geq 1$ and a ring isomorphism $e$ from the adic completion of $\mathcal{O}_{X_0,x_0}$ at its maximal ideal onto $\widehat{A_0}[[u,v]]/(uv - \varpi_0^{w})$, carrying the image of each $a \in A_0$ to the corresponding constant; and a set $S$ of places of $F/L$ (valuation subrings of $F$ containing $L$, proper, with principal ideals) characterised by: $P \in S$ precisely when every $f$ in $\varphi^{-1}(\mathcal{O}_{X,x})$ lies in the valuation subring of $P$, its evaluation $P.\mathrm{evalAt}\,f \in L$ lies in $A$, and that element is a unit of $A$ exactly when $f$ is invertible in $\varphi^{-1}(\mathcal{O}_{X,x})$. Then every $f \in \varphi^{-1}(\mathcal{O}_{X,x})$ lies in the integers of $R_1$, in the integers of $R_2$, and in the valuation subring of every $P \in S$; and $\mathrm{algebraMap}\,L\,F(a) \in \varphi^{-1}(\mathcal{O}_{X,x})$ for every $a \in A$.
--
--   This is the easy half of the description of the local ring at an ordinary double point of a semistable model: the node ring is contained in the two branch rings and in every place centred at the node, and contains the constants from the base. It feeds the analysis of node coordinates and branches at a crossing point, where the reverse inclusion is established separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
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
    (S : Set (Place L F))
    (hS : ∀ P : Place L F, P ∈ S ↔
      ∀ f : F, f ∈ SemistableModel.localRing X φ x → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
        (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1))
    :
    (∀ f : F, f ∈ SemistableModel.localRing X φ x → f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring) ∧
      (∀ a : ↥A, algebraMap L F (a : L) ∈ SemistableModel.localRing X φ x) := by sorry
