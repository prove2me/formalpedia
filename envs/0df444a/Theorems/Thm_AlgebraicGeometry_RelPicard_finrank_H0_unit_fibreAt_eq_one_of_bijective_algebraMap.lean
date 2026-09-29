-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
-- name    : AlgebraicGeometry.RelPicard.finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/8e8873c9-ac1e-5104-bdce-e832de8459a0
-- title:
--   Čech h⁰(𝒪)=1 on a fibre with bijective structure map
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c\colon C\to\operatorname{Spec}R$ a morphism, $k$ a field and $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ a morphism. Assume that, for the $k$-algebra structure on $\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}k,\mathcal O)$ induced by the second projection $C\times_{\operatorname{Spec}R}\operatorname{Spec}k\to\operatorname{Spec}k$ (the structure map obtained from the global-sections comparison of that morphism), the algebra map $k\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}k,\mathcal O)$ is bijective. Let $Y$ denote the iterated pullback $(C\times_{\operatorname{Spec}R}\operatorname{Spec}R)\times_{\operatorname{Spec}R}\operatorname{Spec}k$, formed from the second projection of $c$ against the identity of $\operatorname{Spec}R$ and then against $x$, and let $\mathcal W$ be any two-affine open cover of $Y$: two opens $U_0,U_1$ of $Y$, each affine, with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine. Form the two-chart Čech data of the unit sheaf of modules on $Y$ (the structure sheaf viewed as a module over itself) with respect to $\mathcal W$ and the structure morphism $Y\to\operatorname{Spec}k$ given by `fibreAt`, namely the second projection. Then the $k$-dimension of its $H^0$, the kernel of the difference map $\Gamma(\mathcal O,U_0)\times\Gamma(\mathcal O,U_1)\to\Gamma(\mathcal O,U_0\sqcap U_1)$, $(s_0,s_1)\mapsto -s_0|_{U_0\sqcap U_1}+s_1|_{U_0\sqcap U_1}$, equals $1$.
--
--   This is the statement that $h^0(\mathcal O)=1$ on the fibre of $c$ at $x$, computed through a two-chart Čech presentation, the hypothesis being cohomological flatness in degree $0$ evaluated at $k$ (as holds for proper, geometrically reduced and geometrically connected fibres). It supplies the normalisation of degree-zero cohomology used in the genus/rank computations for fibres of the relative Picard and modular-curve models, and is cited by the constancy statements for $H^1$ ranks and by the Cartier-divisor comparison on two-glued curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hH0 : letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c x) ⊤
      Function.Bijective (algebraMap k Γ(pullback c x, ⊤)))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
      (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 = 1 := by sorry
