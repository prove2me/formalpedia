-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat
-- name    : AlgebraicGeometry.SmallExtension.exists_injective_isTangentOfPair_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/265006e0-c86f-5860-845c-0e4802533ab6
-- title:
--   Lifts agreeing modulo I inject into tangent fields
-- statement:
--   Let $T'$ be an Artinian local ring, $I \subseteq \mathfrak m_{T'}$ an ideal with $I\,\mathfrak m_{T'}=0$, and let $V$ be an abelian group carrying commuting left and right actions of the residue field $k=\mathrm{ResidueField}\,T'$ agreeing by centrality, together with a $T'$-module structure compatible via the scalar tower, and $\iota : V \to T'$ an injective $T'$-linear map whose range is $I$ viewed as a $T'$-submodule. Let $q : Y \to \operatorname{Spec} T'$ be flat, and let $i_0 : Y_0 \to Y$ over $\operatorname{Spec}(T'/I)$, $i_k : Y_k \to Y$ over $\operatorname{Spec} k$, and $q_1 : Z \to Y_k$, $q_2 : Z \to \operatorname{Spec}(k \oplus V)$ be given as pullback squares presenting $Y_0 = Y \times_{T'} \operatorname{Spec}(T'/I)$, $Y_k = Y\times_{T'}\operatorname{Spec} k$ and $Z = Y_k \times_{k} \operatorname{Spec}(\mathrm{TrivSqZeroExt}\,k\,V)$. Then there is an operation $\Phi$ which, for every scheme $A$ with a morphism $p_A : A \to \operatorname{Spec} T'$ and every $u : Y \to A$ with $u$ followed by $p_A$ equal to $q$, maps the set of $v : Y \to A$ over $\operatorname{Spec} T'$ with $i_0 \circ v = i_0 \circ u$ into the set of $w : Z \to A$ whose restriction along the zero section `SquareZero.zeroSection V f₀ q₁ q₂ hZ` of $q_1$ equals $i_k$ followed by $u$, such that: each such map is injective; $u$ itself is sent to $q_1$ followed by $i_k$ followed by $u$; $\Phi$ is natural in $A$, i.e. for $g : A \to A'$ with $g$ followed by $p_{A'}$ equal to $p_A$ one has $\Phi_{p_{A'}}(u \circ g)(v \circ g) = \Phi_{p_A}(u)(v)$ followed by $g$; and, finally, $\Phi$ computes tangent fields on flat affine charts: for any flat $T'$-algebra $C$ and any $c : \operatorname{Spec} C \to Y$ over $\operatorname{Spec} T'$ whose image lies in some affine open of $Y$, and any $c_Z : \operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C) \to Z$ with $c_Z$ followed by $q_1$ and $i_k$ equal to `SmallExtension.thickeningFst` followed by $\operatorname{Spec}$ of `SmallExtension.toReduction` followed by $c$, and $c_Z$ followed by $q_2$ equal to `SmallExtension.thickeningSnd`, the predicate `SmallExtension.IsTangentOfPair I V ι C` holds for the triple $(c \circ u,\; c \circ v,\; c_Z \circ \Phi_{p_A}(u)(v))$: that is, there are a ring homomorphism $\vartheta$ from the fibre product subring $\{(a,b) \in C \times C : a \equiv b \bmod I\!\cdot\!C\}$ to $(k \otimes_{T'} C) \otimes_k \mathrm{TrivSqZeroExt}\,k\,V$ sending $(a,a)$ to $\bar a \otimes 1$ and $(0, \iota(v)\,a)$ to $\bar a \otimes \mathrm{inr}\,v$, and a morphism $\varphi$ from the spectrum of that subring to $A$ pulling back to $c \circ u$ and $c \circ v$ along the two projections and with $c_Z \circ \Phi_{p_A}(u)(v) = \operatorname{Spec}(\vartheta)$ followed by $\varphi$.
--
--   This is the scheme-level form of the small-extension dictionary of deformation theory: over a flat $T'$-scheme $Y$, the lifts $v$ of a morphism that agree with $u$ on the reduction modulo $I$ are recorded injectively, and naturally in the target, by tangent fields on the thickened special fibre $Z = Y_k \times_k \operatorname{Spec}(k \oplus V)$, compatibly with the chartwise notion `SmallExtension.IsTangentOfPair`. It is used in the rigidity statements [`GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot) and its variant for an arbitrary residue field, where two morphisms agreeing modulo a small ideal and along a section are shown to coincide.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_injective_isTangentOfPair_of_flat.lean

import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct

universe u

theorem AlgebraicGeometry.SmallExtension.exists_injective_isTangentOfPair_of_flat
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [Flat q]

    {Y₀ : Scheme.{u}} (i₀ : Y₀ ⟶ Y) (q₀ : Y₀ ⟶ Spec (CommRingCat.of (T' ⧸ I)))
    (h₀ : IsPullback i₀ q₀ q (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))

    {Yk : Scheme.{u}} (ik : Yk ⟶ Y) (f₀ : Yk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hk : IsPullback ik f₀ q (Spec.map (CommRingCat.ofHom (residue T'))))
    {Z : Scheme.{u}} (q₁ : Z ⟶ Yk) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') V)
    (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') V))
    :
    ∃ Φ : ∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u} →
          {w : Z ⟶ A // SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w = ik ≫ u},

      (∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        Function.Injective (Φ pA u hu)) ∧

      (∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q),
        (Φ pA u hu ⟨u, hu, rfl⟩).1 = q₁ ≫ ik ≫ u) ∧

      (∀ {A A' : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (pA' : A' ⟶ Spec (CommRingCat.of T'))
        (g : A ⟶ A') (hg : g ≫ pA' = pA) (u : Y ⟶ A) (hu : u ≫ pA = q)
        (v : {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u}),
        (Φ pA' (u ≫ g) (by rw [Category.assoc, hg, hu])
            ⟨v.1 ≫ g, by rw [Category.assoc, hg, v.2.1], by rw [← Category.assoc, v.2.2, Category.assoc]⟩).1 =
          (Φ pA u hu v).1 ≫ g) ∧

      ∀ {A : Scheme.{u}} (pA : A ⟶ Spec (CommRingCat.of T')) (u : Y ⟶ A) (hu : u ≫ pA = q)
        (v : {v : Y ⟶ A // v ≫ pA = q ∧ i₀ ≫ v = i₀ ≫ u})
        (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
        (c : Spec (CommRingCat.of C) ⟶ Y) (hc : c ≫ q = Spec.map (CommRingCat.ofHom (algebraMap T' C))),
        (∃ U : Y.Opens, IsAffineOpen U ∧ Set.range c.base ⊆ (U : Set Y)) →
        ∀ (cZ : Spec (CommRingCat.of (SmallExtension.thickening T' V C)) ⟶ Z),
        cZ ≫ q₁ ≫ ik = SmallExtension.thickeningFst T' V C ≫
          Spec.map (CommRingCat.ofHom (SmallExtension.toReduction T' C)) ≫ c →
        cZ ≫ q₂ = SmallExtension.thickeningSnd T' V C →
        SmallExtension.IsTangentOfPair I V ι C (c ≫ u) (c ≫ v.1) (cZ ≫ (Φ pA u hu v).1) := by sorry
