-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/2e21d13b-ff35-59a4-b535-101bb4e94cf6
-- title:
--   Multiplicativity of Čech Euler characteristics over a product
-- statement:
--   Let $K$ be a field and let $X$, $Y$ be schemes (in universe $0$) equipped with morphisms $\pi_X : X \to \operatorname{Spec} K$ and $\pi_Y : Y \to \operatorname{Spec} K$, both assumed proper. Let $F$ be a module over the structure sheaf of $X$ and $G$ one over that of $Y$, each assumed invertible in the sense that every point has an open neighbourhood $U$ over which the pullback along the inclusion $U \hookrightarrow X$ (resp. $U \hookrightarrow Y$) is isomorphic to the unit sheaf of modules on $U$. Let $\mathfrak{U}$, $\mathfrak{V}$ and $\mathfrak{W}$ be ordered affine covers of $X$, $Y$ and of the fibre product $X \times_{\operatorname{Spec} K} Y$ respectively; an ordered affine cover consists of a finite linearly ordered index type together with affine opens indexed by it whose supremum is the whole scheme. Consider the $\mathcal{O}$-module presheaf $U \mapsto \Gamma(M, U)$, with its $K$-module structure coming from the structure morphism and the evident restriction maps, attached to a module $M$; write $\chi$ for the Euler characteristic of such a presheaf relative to an ordered affine cover, namely the alternating sum $\sum_{i < n} (-1)^i \dim_K \check H^i$ of the $K$-dimensions of the Čech cohomology of the cover, taken over degrees below the number of charts. The assertion is that for the module $p_1^* F \otimes p_2^* G$ on $X \times_{\operatorname{Spec} K} Y$, viewed over $K$ via $p_1$ followed by $\pi_X$, one has $\chi(\mathfrak{W}, p_1^* F \otimes p_2^* G) = \chi(\mathfrak{U}, F) \cdot \chi(\mathfrak{V}, G)$, where $p_1$, $p_2$ are the two projections of the fibre product.
--
--   This is the Künneth formula at the level of Euler characteristics: the Euler characteristic of an exterior tensor product of invertible sheaves on a product of proper schemes over a field is the product of the two Euler characteristics. It feeds the numerical computations of Euler characteristics of line bundles on abelian schemes, being used in the computation relating $\chi(L) \chi(L^{\vee})$ to a signed rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper
    {K : Type} [Field K] {X Y : Scheme.{0}}
    (πX : X ⟶ Spec (CommRingCat.of K)) (πY : Y ⟶ Spec (CommRingCat.of K)) [IsProper πX] [IsProper πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G)
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) (𝔚 : (pullback πX πY).OrderedAffineCover) :
    (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
        ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
          (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).eulerChar 𝔚 =
      (OModulePresheaf.ofModules πX F).eulerChar 𝔘 * (OModulePresheaf.ofModules πY G).eulerChar 𝔙 := by sorry
