-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
-- name    : AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/4673da8a-da8b-5845-8649-2ab929aa93d5
-- title:
--   Fibrewise criterion for local freeness of π_*F over a finite-type base
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c \colon C \to \operatorname{Spec} R$ be proper and smooth of relative dimension one, with $\varepsilon$ a section, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume the degrees of the available finite-map chart data are unbounded: for every $m_0 \in \mathbb N$ there is a datum $\mathfrak F$ of type `FiniteMapData c ε` with $m_0 \le \mathfrak F.m$, that is, affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose basic opens both equal $U \cap V$ and whose restrictions there are mutually inverse, with $f$ and $g$ making $\Gamma(C,U)$, $\Gamma(C,V)$ finite over $R[T]$, and with all level sets of $f$ over local $R$-algebras finite free of rank $\mathfrak F.m$. Let $A$ be an $R$-algebra of finite type, put $C_A = C \times_{\operatorname{Spec} R} \operatorname{Spec} A$, and let $F$ be a module on $C_A$ that is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $F$ is isomorphic to the unit sheaf of modules. Let $n \in \mathbb N$, and assume that for every field $k$, every morphism $s \colon \operatorname{Spec} k \to \operatorname{Spec} A$ and every cover of the fibre $(C_A)_s$ by two affine opens with affine intersection, the associated two-chart Čech complex of the pulled-back module $F_s$ has $H^1$ a subsingleton and $\dim_k H^0 = n$, where $H^0$ is the kernel of the Čech difference on the product of the sections over the two charts and $H^1$ is the sections over the intersection modulo its image. Then the pushforward of $F$ along the projection $C_A \to \operatorname{Spec} A$ is locally free of rank $n$: every point of $\operatorname{Spec} A$ has an open neighbourhood on which this pushforward becomes isomorphic to the free module sheaf on $n$ generators.
--
--   This is the cohomology-and-base-change criterion for a smooth proper relative curve, in the form: fibrewise vanishing of $H^1$ together with constant fibre dimension $h^0 = n$ forces the pushforward to be locally free of rank $n$. It is the affine-base case used to derive the corresponding statement [`AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre) over a general base locally of finite type over $\operatorname{Spec} R$, which in turn supports the representability arguments for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (F : (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Modules)
    (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (𝒲 : (pullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
        (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
          (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n
      ((Scheme.Modules.pushforward (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj F) := by sorry
