-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed
-- name    : AlgebraicCurve.mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/06af3420-3677-5584-a36a-111fb648ca00
-- title:
--   Functions integral on both branches are regular above the node
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring such that for all $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is an $n \in \mathbb{N}$ with $b \mid a^{n}$. Let $F/L$ be a field extension that is essentially of finite type and is a curve over $L$ in the sense of `IsCurveOver`: every nonzero $f \in F$ has a degree-zero divisor given by the orders $v(f)$ at the places $v$ (a place being a valuation subring of $F$ containing $L$, different from $F$, whose ideals are principal), each place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$. Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism $\mathrm{toBase} \colon X \to \operatorname{Spec} A$ all of whose stalks are integrally closed, and let $\varphi \colon F \cong K(X)$ be a ring isomorphism sending the image of $a \in A$ in $F$ to the germ at the generic point of the global section attached to $a$ by $\mathrm{toBase}$. Descent data are fixed: a discrete valuation ring $A_0$ with uniformiser $\varpi_0$ generating its maximal ideal, an injective local homomorphism $\iota_0 \colon A_0 \to A$ with every element of $A$ algebraic over the image subring, an integral scheme $X_0$ proper, flat and locally of finite presentation over $\operatorname{Spec} A_0$, and an isomorphism $X \cong X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ compatible with $\mathrm{toBase}$. Let $x \in X$ be a closed point (its only specialisation is itself) lying over the closed point of $\operatorname{Spec} A$, and let $\eta_1 \neq \eta_2$ be two distinct proper generisations of $x$ such that every proper generisation of $x$ lying over the closed point of $\operatorname{Spec} A$ is $\eta_1$ or $\eta_2$. For $i = 1,2$ let $\bar F_i$ be a field over the residue field of $A$ and $R_i$ a `RegularProlongation` of $A$ to $F$ with residue field $\bar F_i$ — a valuation subring $R_i.\mathrm{integers}$ of $F$ contracting to $A$ on $L$, with a surjective residue map to $\bar F_i$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero $f \in F$ can be scaled by some $c \in L$ into $R_i.\mathrm{integers}$ with nonzero residue — and assume $R_i.\mathrm{integers}$ equals, as a subring of $F$, the image under $\varphi^{-1}$ of the stalk of $X$ at $\eta_i$ inside $K(X)$. Let $x_0 \in X_0$ be the image of $x$ under the isomorphism followed by the projection to $X_0$, let $w \geq 1$, and assume a ring isomorphism $e$ from the adic completion of the stalk of $X_0$ at $x_0$ along its maximal ideal onto the crossing model $\widehat{A_0}[[u,v]]/(uv - \varpi_0^{w})$, where $\widehat{A_0}$ is the adic completion of $A_0$, which sends the image of each $a \in A_0$ (via the structure morphism and the germ at $x_0$) to the class of the constant $a$. Finally let $S$ be the set of places $P$ of $F/L$ characterised by: $P \in S$ if and only if every $f$ in the local ring of $X$ at $x$ (the image in $F$ of the stalk at $x$) lies in $P$'s valuation subring and, its evaluation $P.\mathrm{evalAt}\,f \in L$ lying in $A$, that evaluation is a unit of $A$ exactly when $f$ is invertible in the local ring of $X$ at $x$. The conclusion is that any $f \in F$ lying in $R_1.\mathrm{integers}$, in $R_2.\mathrm{integers}$ and in the valuation subring of every $P \in S$ lies in the local ring of $X$ at $y$, for every proper generisation $y \neq x$ of $x$.
--
--   This is the local statement, at a point of the special fibre whose completed local ring is a crossing $uv = \varpi_0^{w}$, that a rational function which is integral along both branches through the node and at all the places centred at the node is regular at every generisation of that node. It feeds the assembly step [`AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed`](thm.html#AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed), where the local rings of a semistable model are identified with the prescribed valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed
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
      ∀ y : X, y ⤳ x → y ≠ x → f ∈ SemistableModel.localRing X φ y := by sorry
