-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
-- name    : AlgebraicCurve.exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/c8e39c69-ffb6-542a-97fb-7f45b027805b
-- title:
--   Branch places and node coordinates at an ordinary double point
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring such that for $a,b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$; let $F/L$ be a field which is a curve over $L$ (principal divisors of degree zero, residue fields of places finite over $L$, $\Omega_{F/L}$ free of rank one) and essentially of finite type over $L$. Let $X$ be an integral scheme with a proper, flat, locally of finite presentation morphism `toBase` to $\operatorname{Spec} A$, all of whose stalks are integrally closed, and $\varphi : F \cong \Gamma_{X}$ an isomorphism onto the function field carrying $a \in A$ to its image under the structure map. Descent data: a henselian discrete valuation domain $A_{0}$ with uniformiser $\varpi_{0}$, an injective local homomorphism $\iota_{0} : A_{0} \to A$ inducing a surjection onto the residue field of $A$ and with $A$ algebraic over $\iota_{0}(A_{0})$, and an integral $X_{0}$ proper, flat and locally of finite presentation over $\operatorname{Spec} A_{0}$ together with an isomorphism of $X$ with the pullback of $X_{0}$ along $\operatorname{Spec} \iota_{0}$ compatible with the structure morphisms. Point data: a closed point $x$ of $X$ (no $y \neq x$ generises it) lying over the closed point of $A$, and two distinct points $\eta_{1} \neq \eta_{2}$, both $\neq x$, specialising to $x$, such that any point of the special fibre other than $x$ specialising to $x$ is $\eta_{1}$ or $\eta_{2}$; fields $\bar F_{1}, \bar F_{2}$ over the residue field of $A$ and regular prolongations $R_{1}, R_{2}$ of $A$ to $F$ with values in $\bar F_{1}, \bar F_{2}$ (each given by a valuation subring `integers` of $F$ meeting $L$ exactly in $A$, together with a surjective residue homomorphism onto $\bar F_{i}$ with kernel the maximal ideal, compatible with the residue map of $A$, and such that every nonzero $f \in F$ has an $L$-multiple with nonzero residue) whose rings of integers are, as subrings of $F$, the local rings $\mathcal{O}_{X,\eta_{i}}$ transported by $\varphi$. Finally let $x_{0}$ be the image of $x$ in $X_{0}$, $w \geq 1$ an integer invertible in $A_{0}$, and $e$ a ring isomorphism of the adic completion of $\mathcal{O}_{X_{0},x_{0}}$ with the crossing model $\widehat{A_{0}}[[u,v]]/(uv - \varpi_{0}^{w})$ carrying the images of elements of $A_{0}$ to the corresponding constants. Writing $\mathcal{N} \subseteq F$ for the local ring $\mathcal{O}_{X,x}$ transported by $\varphi$, the conclusion asserts the existence of places $x_{1}$ of $\bar F_{1}$ and $x_{2}$ of $\bar F_{2}$ over the residue field of $A$, a set $S$ of places of $F$ over $L$, and elements $x_{n}, y_{n}, u \in F$ such that: $P \in S$ exactly when every $f \in \mathcal{N}$ lies in the valuation subring of $P$ with value $P.\mathrm{evalAt}\,f$ in $A$, this value being a unit of $A$ if and only if $f$ is invertible in $\mathcal{N}$; $\mathcal{N}$ consists precisely of the $f$ lying in $R_{1}.\mathrm{integers}$, in $R_{2}.\mathrm{integers}$ and in the valuation subring of every $P \in S$; $\mathcal{N}$ contains the image of $A$; $x_{n}, y_{n}, u \in \mathcal{N}$ with $u$ invertible in $\mathcal{N}$, the $R_{1}$-residue of $x_{n}$ and the $R_{2}$-residue of $y_{n}$ vanish, the $R_{2}$-residue of $x_{n}$ has order $1$ at $x_{2}$ and the $R_{1}$-residue of $y_{n}$ has order $1$ at $x_{1}$, and $x_{n} y_{n} = \iota_{0}(\varpi_{0})^{w} u$ in $F$; $x_{i}$ is the only place of $\bar F_{i}$ whose valuation subring contains all residues of elements of $\mathcal{N}$; every $f \in \mathcal{N}$ has $R_{1}$- and $R_{2}$-residues regular at $x_{1}$ and $x_{2}$ whose residues there are the images of one common element of the residue field of $A$; and conversely every pair $g_{1}, g_{2}$ regular at $x_{1}, x_{2}$ with residues coming from a common element of the residue field of $A$ is the pair of residues of some $f \in \mathcal{N}$.
--
--   This is the local description of a proper flat model at an ordinary double point of its special fibre, in the form used for semistable curves by Bosch–Lütkebohmert and Deligne–Rapoport: the local ring at the node is the fibre product of the two branch local rings over the residue field of $A$, and it carries node coordinates $x_n y_n = \varpi_0^{w} u$ with prescribed vanishing on the two branches. It is used in the assembly of semistable models of full-level modular curves by descent from a tame henselian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (hres₀ : Function.Surjective ((IsLocalRing.residue ↥A).comp ι₀))
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
    (w : ℕ) (hw : 1 ≤ w) (hwu : IsUnit ((w : ℕ) : A₀))
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a)) :
    let 𝒩 : Subring F := SemistableModel.localRing X φ x
    ∃ (x₁ : Place (ResidueField ↥A) Fbar₁) (x₂ : Place (ResidueField ↥A) Fbar₂) (S : Set (Place L F)) (xn yn u : F),

      (∀ P : Place L F, P ∈ S ↔
        ∀ f : F, f ∈ 𝒩 → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ 𝒩, f * g = 1)) ∧

      (∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring) ∧
      (∀ a : ↥A, algebraMap L F (a : L) ∈ 𝒩) ∧

      xn ∈ 𝒩 ∧ yn ∈ 𝒩 ∧ u ∈ 𝒩 ∧ (∃ u' ∈ 𝒩, u * u' = 1) ∧
      (∀ h₁ : xn ∈ R₁.integers, R₁.residue ⟨xn, h₁⟩ = 0) ∧
      (∀ h₂ : xn ∈ R₂.integers, x₂.ord (R₂.residue ⟨xn, h₂⟩) = 1) ∧
      (∀ h₂ : yn ∈ R₂.integers, R₂.residue ⟨yn, h₂⟩ = 0) ∧
      (∀ h₁ : yn ∈ R₁.integers, x₁.ord (R₁.residue ⟨yn, h₁⟩) = 1) ∧
      xn * yn = algebraMap L F ((ι₀ ϖ₀ : ↥A) : L) ^ w * u ∧

      (∀ Q' : Place (ResidueField ↥A) Fbar₁,
        (∀ (f : F) (hf : f ∈ R₁.integers), f ∈ 𝒩 → R₁.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) → Q' = x₁) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar₂,
        (∀ (f : F) (hf : f ∈ R₂.integers), f ∈ 𝒩 → R₂.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) → Q' = x₂) ∧

      (∀ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers), f ∈ 𝒩 →
        ∃ (m₁ : R₁.residue ⟨f, hf₁⟩ ∈ x₁.toValuationSubring) (m₂ : R₂.residue ⟨f, hf₂⟩ ∈ x₂.toValuationSubring)
          (c : ResidueField ↥A),
          IsLocalRing.residue ↥x₁.toValuationSubring ⟨_, m₁⟩ = algebraMap (ResidueField ↥A) x₁.ResidueField c ∧
          IsLocalRing.residue ↥x₂.toValuationSubring ⟨_, m₂⟩ = algebraMap (ResidueField ↥A) x₂.ResidueField c) ∧

      (∀ (g₁ : Fbar₁) (g₂ : Fbar₂) (m₁ : g₁ ∈ x₁.toValuationSubring) (m₂ : g₂ ∈ x₂.toValuationSubring) (c : ResidueField ↥A),
        IsLocalRing.residue ↥x₁.toValuationSubring ⟨g₁, m₁⟩ = algebraMap (ResidueField ↥A) x₁.ResidueField c →
        IsLocalRing.residue ↥x₂.toValuationSubring ⟨g₂, m₂⟩ = algebraMap (ResidueField ↥A) x₂.ResidueField c →
          ∃ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers), f ∈ 𝒩 ∧
            R₁.residue ⟨f, hf₁⟩ = g₁ ∧ R₂.residue ⟨f, hf₂⟩ = g₂) := by sorry
