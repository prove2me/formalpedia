-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/f4e82398-a2f4-527c-9e6f-06875a12e568
-- title:
--   Counit nonzero on every fibre when h¹=0, h⁰=1
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a proper flat morphism of schemes, and let $\mathcal{V}$ be a two-affine open cover of $C$, i.e. two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $t \colon T \to \operatorname{Spec} R$ be locally of finite type and let $M$ be a sheaf of modules on $C \times_{\operatorname{Spec} R} T$ which is invertible in the sense that every point has an open neighbourhood $U$ with $M|_U$ isomorphic to the unit module on $U$. Assume that for every field $k$, every $s \colon \operatorname{Spec} k \to T$ and every two-affine open cover $\mathcal{W}$ of the fibre product $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ over the second projection, the two-term Čech complex of the pulled-back module $\mathrm{fibreModule}\,c\,t\,s\,M$ on $\mathcal{W}$, taken relative to the structure map $\mathrm{fibreAt}\,c\,t\,s$ to $\operatorname{Spec} k$, has $H^1 = M_{01}/\operatorname{im}(d)$ a subsingleton and $H^0 = \ker(d) \subseteq M_0 \times M_1$ of $k$-dimension $1$. Then for every field $k$ and every $x \colon \operatorname{Spec} k \to T$, the pullback along $\mathrm{mapOnProdOver}\,c\,x\,\mathrm{rfl} \colon C \times_{\operatorname{Spec} R} \operatorname{Spec} k \to C \times_{\operatorname{Spec} R} T$ (identity on $C$, $x$ on the second factor) of the counit component at $M$ of the pullback–pushforward adjunction along $\mathrm{pr}_2 \colon C \times_{\operatorname{Spec} R} T \to T$ is a nonzero morphism of modules.
--
--   This is the fibrewise nonvanishing statement extracted from cohomology and base change: under the Čech hypotheses $h^1 = 0$, $h^0 = 1$ on all field-valued fibres, the evaluation map $\mathrm{pr}_2^* \mathrm{pr}_{2*} M \to M$ does not vanish after restriction to any fibre $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$. It supplies the nonvanishing input used when a rigidified line bundle with these fibre invariants is cut out by its canonical section, and is cited in the construction of representing objects for the relative sub-Picard functors attached to two-chart degenerations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) ≠ 0 := by sorry
