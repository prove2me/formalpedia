-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_openCharts_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_openCharts_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/a20cd51c-e458-5a04-b8b9-1479d9735c28
-- title:
--   Representability of Pic⁰ cut by open charts
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c\colon C\to\operatorname{Spec}R$ be a proper flat morphism of schemes, let $\mathcal{V}$ be a two-affine open cover of $C$ (two affine opens with affine intersection whose union is $C$), and let $\varepsilon$ be a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ c=\mathrm{id}$. Assume: (hH0) for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\mathcal{O})$, for the algebra structure coming from the second projection, is bijective; (hfib) for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every module $L$ on $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ that is invertible (locally isomorphic to the unit sheaf) and satisfies `IsAlgEquivZero` for the projection to $\operatorname{Spec}k$ — that is, $L$ is the fibre at one $k$-point of an invertible module on a base change by a geometrically integral morphism locally of finite type whose fibre at another $k$-point is trivial — any nonzero map from the monoidal unit to $L$ forces $L$ to be isomorphic to the unit. Assume further a finite index type $\iota$, quasi-compact schemes $X_i$, and morphisms $f_i$ from the lifted Yoneda presheaf of $X_i$ to the total presheaf $T\mapsto\coprod_{t\colon T\to\operatorname{Spec}R}$ (classes of rigidified line bundles on $C\times_{\operatorname{Spec}R}T$ satisfying the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`), each $f_i$ relatively representable by open immersions, each induced morphism $X_i\to\operatorname{Spec}R$ locally of finite type, and the induced map from the coproduct Zariski-locally surjective. Then there is a designation $D$, consisting of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec}R$ and a section, which represents the cut: there is a Poincaré rigidified line bundle over $D.\mathrm{toBase}$ satisfying the condition, every rigidified line bundle over $t\colon T\to\operatorname{Spec}R$ satisfying the condition is the pullback of the Poincaré bundle along a unique $T\to D.P$ over $\operatorname{Spec}R$, and the pullback along the zero section is trivial; moreover $D.\mathrm{toBase}$ is smooth, separated and quasi-compact.
--
--   This is the base-generic representability statement for the relative $\operatorname{Pic}^0$ of a proper flat pointed curve with universally trivial $H^0$: once open charts of the cut functor are produced, they glue to a smooth separated quasi-compact group-scheme-to-be over $\operatorname{Spec}R$. It is the construction used to build the relative Jacobian in the smooth case and for proper flat semistable curves, and is invoked by the statements producing Jacobians from chart data and from degeneration models over localisations away from a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_openCharts_of_bijective_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_JacJ1Iface
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_RelSubPicGlue
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_openCharts_of_bijective_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : (pullback c x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd c x) L →
      ∀ s : 𝟙_ (pullback c x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback c x).Modules))
    {ι : Type u} [Finite ι] (X : ι → Scheme.{u}) [∀ i, CompactSpace (X i)]
    (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal)
    (hf : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i))
    (hft : ∀ i, LocallyOfFiniteType (uliftYonedaEquiv (f i)).1)
    (hsurj : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f)) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase := by sorry
