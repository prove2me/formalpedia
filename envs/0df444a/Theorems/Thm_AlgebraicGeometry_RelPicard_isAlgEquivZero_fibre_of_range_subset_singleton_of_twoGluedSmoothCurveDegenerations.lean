-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/45329840-edb9-5cc5-8999-519aa77bcf8f
-- title:
--   Point-independence of algebraic equivalence to zero, two-curve degenerations
-- statement:
--   Let $R$ be a Noetherian commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper flat morphism, equipped with a `TwoAffineOpenCover` of $C$ (two affine opens with affine intersection whose join is everything), and assume that for every $R$-algebra $A$ the structural map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ is bijective. Let $U\subseteq C$ be open with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$ whose image lies in $U$. Assume: every geometric fibre that is smooth is contained in $U$ (hgoodU); every geometric fibre $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$, $k$ algebraically closed, is reduced; there is $g\in\mathbb N$ such that for every algebraically closed $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every two-affine open cover of the fibre, the $k$-dimension of the two-chart Čech $H^1$ of the structure sheaf is $g$; and for every algebraically closed $k$ and $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ with non-smooth fibre there are proper smooth geometrically integral curves $c_1\colon C_1\to\operatorname{Spec}k$, $c_2\colon C_2\to\operatorname{Spec}k$ and closed immersions $i_1,i_2$ into the fibre over $s$, compatible with the structure maps, together with $n\in\mathbb N$, such that the two images cover the fibre, $C_1\times_{C_s}C_2$ is reduced with $n>0$ points, $\varepsilon(s)$ lies in the image of $i_1$ but not of $i_2$, the preimage of $U$ in the fibre is the complement of the crossing locus, the image of $i_1$ meets it in the connected component of $\varepsilon(s)$ and the image of $i_2$ in the complementary part, and each $i_j$ restricted over the complement of the other image is an open immersion onto an open subscheme. Conclusion: for every scheme $T$, every $t\colon T\to\operatorname{Spec}R$ locally of finite type, every rigidified line bundle $L$ on $C\times_{\operatorname{Spec}R}T$ relative to $\varepsilon$ (an invertible module with a trivialisation along the rigidifying section), every point $x\in T$, and any algebraically closed fields $k_1,k_2$ with morphisms $s_i\colon\operatorname{Spec}k_i\to T$ whose set-theoretic images are contained in $\{x\}$: if the pullback of $L.L$ to the fibre of $C_T$ at $s_1$ is algebraically equivalent to zero over $\operatorname{Spec}k_1$ — that is, there are a locally of finite type geometrically integral $h\colon T'\to\operatorname{Spec}k_1$, an invertible module $M$ on the base change along $h$ and two sections $t_0,t_1$ of $h$ whose pullbacks of $M$ are isomorphic to the structure sheaf and to that fibre module respectively — then the same holds for $s_2$ over $\operatorname{Spec}k_2$.
--
--   This is the statement that algebraic equivalence to zero of the fibre of a rigidified line bundle depends only on the underlying point of the base, not on the chosen geometric point above it, for families whose singular geometric fibres are two smooth proper geometrically integral curves crossing in finitely many points. It feeds the construction of the algebraic-equivalence-to-zero locus of the relative Picard functor for such families, being used in the identification of that locus by an open condition and in the local finite presentation surjectivity statement for the associated subfunctor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))

    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))

    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (x : T)
      {k₁ : Type u} [Field k₁] [IsAlgClosed k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T),
      Set.range ⇑s₁ ⊆ {x} → IsAlgEquivZero (fibreAt c t s₁) (fibreModule c t s₁ L.L) →
      ∀ {k₂ : Type u} [Field k₂] [IsAlgClosed k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T),
      Set.range ⇑s₂ ⊆ {x} → IsAlgEquivZero (fibreAt c t s₂) (fibreModule c t s₂ L.L) := by sorry
