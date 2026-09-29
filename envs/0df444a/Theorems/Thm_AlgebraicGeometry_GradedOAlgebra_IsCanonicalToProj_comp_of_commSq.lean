-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_of_commSq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ac8257b5-f2a7-569a-8412-b317c1f77fdb
-- title:
--   Canonical morphism to Proj under base change
-- statement:
--   Let $S$ and $S'$ be commutative rings with $S'$ an $S$-algebra, let $X,X'$ be schemes, and let $f\colon X\to\operatorname{Spec} S$, $f'\colon X'\to\operatorname{Spec} S'$ and $c\colon X'\to X$ be morphisms with $c$ followed by $f$ equal to $f'$ followed by $\operatorname{Spec}$ of the structure map $S\to S'$ (a commuting square only; no pullback property is assumed). Let $L$ be a module on $X$, $L'$ a module on $X'$, and $e\colon c^{*}L\xrightarrow{\ \sim\ }L'$ an isomorphism. Let $R$ be a commutative $S$-algebra graded by submodules $\mathfrak{R}_n$ ($n\in\mathbb N$), let $\iota_n\colon \mathfrak{R}_n\to\Gamma(L^{\otimes n},\top)$ be arbitrary maps, where $L^{\otimes n}$ is the recursively defined tensor power ($L^{\otimes 0}=\mathbf 1$, $L^{\otimes(n+1)}=L^{\otimes n}\otimes L$), and let $\theta\colon X\to\operatorname{Proj}\mathfrak{R}$ satisfy `IsCanonicalToProj f L R 𝓡 ι θ`, i.e. (i) $\theta$ followed by $\operatorname{Proj}\mathfrak{R}\to\operatorname{Spec}\mathfrak{R}_0$ followed by $\operatorname{Spec}$ of the degree-zero projection precomposed with $S\to R$ equals $f$; (ii) for each $n>0$ and $\sigma\in\mathfrak{R}_n$, the section $\iota_n(\sigma)$ is a frame on $\theta^{-1}D_+(\sigma)$, meaning that on every open $W\le\theta^{-1}D_+(\sigma)$ multiplication by the restriction of $\iota_n(\sigma)$ is a bijection $\Gamma(X,W)\to\Gamma(L^{\otimes n},W)$; and (iii) for $n>0$, $\sigma\in\mathfrak{R}_n$, $k\in\mathbb N$ and $s\in\mathfrak{R}_{kn}$, the pullback along $\theta$ of the section $s/\sigma^{k}$ of the structure sheaf on $D_+(\sigma)$ multiplies the restriction of $\iota_{kn}(\sigma^{k})$ to $\theta^{-1}D_+(\sigma)$ into the restriction of $\iota_{kn}(s)$. Then the same predicate holds for the base-changed data: for the morphism $f'$ followed by $\operatorname{Spec}(S\to S')$, the module $L'$, the same graded algebra $\mathfrak{R}$, the maps sending $x\in\mathfrak{R}_n$ to the image of $\iota_n(x)$ under the unit of the adjunction $c^{*}\dashv c_{*}$ at $L^{\otimes n}$ evaluated at $\top$ followed by the comparison isomorphism $c^{*}(L^{\otimes n})\cong (c^{*}L)^{\otimes n}\cong L'^{\otimes n}$ evaluated at $\top$, and the morphism $c$ followed by $\theta$.
--
--   This is the functoriality of the canonical morphism to $\operatorname{Proj}$ of a graded algebra: a morphism to $\operatorname{Proj}\mathfrak{R}$ determined by a line bundle together with a family of sections remains such a morphism after base change along a commuting square of bases. It feeds the comparison results [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp) and [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_comp_projMap_eq`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_comp_projMap_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_of_commSq
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : c ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
    (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) :
    AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) L' R 𝓡
      (fun (n : ℕ) (x : 𝓡 n) =>
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
      (c ≫ θ) := by sorry
