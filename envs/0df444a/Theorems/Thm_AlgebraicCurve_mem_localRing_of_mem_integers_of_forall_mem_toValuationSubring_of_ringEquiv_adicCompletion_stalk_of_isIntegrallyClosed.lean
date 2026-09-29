-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
-- name    : AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/59782302-3159-5b44-a62d-fd6bde47fd5a
-- title:
--   Regularity at a node from integrality on both branches
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring such that for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$. Let $F$ be a field extension of $L$, essentially of finite type, which is a curve over $L$ in the project's sense (every nonzero element has a degree-zero divisor recording its orders at all places, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$). Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism $\mathrm{toBase} \colon X \to \operatorname{Spec} A$ all of whose stalks are integrally closed, and let $\varphi \colon F \cong$ (function field of $X$) be a ring isomorphism carrying $\mathrm{algebraMap}_{L,F}(a)$, for $a \in A$, to the germ at the generic point of the global section $a$ pulled back along $\mathrm{toBase}$. Descent data are given: a discrete valuation ring $A_{0}$ with injective local homomorphism $\iota_{0} \colon A_{0} \to A$, an element $\varpi_{0}$ generating the maximal ideal of $A_{0}$, every element of $A$ algebraic over the image of $\iota_{0}$; an integral $X_{0}$ with $\mathrm{toBase}_{0} \colon X_{0} \to \operatorname{Spec} A_{0}$ proper, flat, locally of finite presentation; and an isomorphism $X \cong X_{0} \times_{\operatorname{Spec} A_{0}} \operatorname{Spec} A$ compatible with the morphisms to $\operatorname{Spec} A$. Let $x \in X$ lie over the closed point of $\operatorname{Spec} A$ and be closed (every $y$ with $x \rightsquigarrow y$ equals $x$), and let $\eta_{1} \neq \eta_{2}$ be points, both distinct from $x$, specialising to $x$, such that every point specialising to $x$, distinct from $x$ and lying over the closed point, is $\eta_{1}$ or $\eta_{2}$. Let $R_{1}, R_{2}$ be regular prolongations of $A$ to $F$ with residue fields $\bar F_{1}, \bar F_{2}$ over the residue field of $A$ (valuation subrings of $F$ inducing $A$ on $L$, together with surjective residue maps onto $\bar F_{i}$ with kernel the maximal ideal, compatible with the residue map of $A$, and such that every nonzero element of $F$ has an $L$-multiple with nonzero residue), whose rings of integers coincide, as subrings of $F$, with the images under $\varphi^{-1}$ of the stalks of $X$ at $\eta_{1}$ and $\eta_{2}$ respectively. Let $x_{0} \in X_{0}$ be the image of $x$ under the first projection, let $w \geq 1$, and let $e$ be a ring isomorphism from the adic completion of the stalk of $X_{0}$ at $x_{0}$ along its maximal ideal onto $W[[u,v]]/(uv - \varpi_{0}^{w})$, where $W$ is the adic completion of $A_{0}$, carrying the image of each $a \in A_{0}$ (as a germ of a global section pulled back along $\mathrm{toBase}_{0}$) to the constant $a$. Finally let $S$ be a set of places of $F/L$ characterised by: $P \in S$ if and only if every $f$ in the subring $\varphi^{-1}(\mathcal O_{X,x}) \subseteq F$ lies in the valuation subring of $P$, its value $P.\mathrm{evalAt}\, f \in L$ (the preimage in $L$ of the residue of $f$) lies in $A$, and that element is a unit of $A$ exactly when $f$ is invertible in $\varphi^{-1}(\mathcal O_{X,x})$. Then every $f \in F$ lying in the integers of $R_{1}$ and of $R_{2}$ and in the valuation subring of every $P \in S$ lies in $\varphi^{-1}(\mathcal O_{X,x})$.
--
--   This is the regularity criterion at an ordinary double point of a semistable model: a function integral along both branches through the node and without poles at the places whose centre is the node is already regular at the node. It feeds into the construction of node coordinates and the analysis of the two branches at $x$ used in the global assembly of a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
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
    ∀ f : F, f ∈ R₁.integers → f ∈ R₂.integers → (∀ P ∈ S, f ∈ P.toValuationSubring) →
      f ∈ SemistableModel.localRing X φ x := by sorry
