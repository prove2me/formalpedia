-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre
-- name    : AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/ff022d07-e4b5-59a5-896e-f7c20d0c61aa
-- title:
--   Fibrewise h⁰=1, h¹=0 forces M≅𝒪(D)otimespr₂^*N
-- statement:
--   Let $R$ be a Noetherian commutative ring and $c : C \to \operatorname{Spec} R$ a proper morphism, smooth of relative dimension $1$ and geometrically integral, equipped with a section $\varepsilon$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume the weak finite-map hypothesis `h𝔉`: for every $m_0$ there are data `SmoothProperCurve.FiniteMapData c ε` with level-set degree $m \ge m_0$, namely affine opens $U, V$ with $U \sqcup V = C$, $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ with $U \cap V = C_f = C_g$ and $f\cdot g = 1$ there, $R[X] \to \Gamma(C,U)$ and $R[X] \to \Gamma(C,V)$ (via $f$, resp. $g$) finite, and all level sets $S \otimes_R \Gamma(C,U)/(1\otimes f - s\otimes 1)$ free of rank $m$ over every local $R$-algebra $S$. Let $g \in \mathbb{N}$ be such that for every algebraically closed field $k$, every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ and every cover of the fibre $C \times_{\operatorname{Spec} R} \operatorname{Spec} R$ pulled back along $x$ by two affine opens with affine intersection, the two-chart Čech $H^1$ of the structure sheaf (the monoidal unit) has $k$-dimension $g$. Let $t : T \to \operatorname{Spec} R$ be locally of finite type and let $M$ be a module on $C \times_{\operatorname{Spec} R} T$ which is invertible (every point has a neighbourhood on which $M$ restricts to the unit module); assume that for every field $k$, every $s : \operatorname{Spec} k \to T$ and every two-affine cover $\mathcal W$ of the fibre $(C\times_{\operatorname{Spec} R} T)\times_T \operatorname{Spec} k$, the Čech $H^1$ of the pulled-back module is a subsingleton and its $H^0$ has $k$-dimension $1$. Then there are a relative effective Cartier divisor $D$ of degree $g$ on $C \times_{\operatorname{Spec} R} T$ over $T$ — an ideal sheaf datum $D.I$ whose closed subscheme is finite, flat and locally of finite presentation over $T$ with fibre rank $g$ at every point of $T$ — and an invertible module $N$ on $T$ such that the dual of $D.I$ is isomorphic to $M \otimes \mathrm{pr}_2^* N$; moreover $D.I$ is unique with this property: any relative effective Cartier divisor $D'$ of any degree $d'$ whose associated line bundle is isomorphic to $M \otimes \mathrm{pr}_2^* N'$ for some invertible $N'$ on $T$ satisfies $D'.I = D.I$.
--
--   This is the step producing the divisor attached to a fibrewise-nondegenerate line bundle in the construction of open charts on the relative Picard scheme (Jacobian) of a smooth proper curve with a section; the degree of the divisor is the genus $g$ of the geometric fibres. It is used by [`AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1`](thm.html#AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1), where the fibrewise hypotheses are verified after twisting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1) :
    ∃ (D : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N ∧
      Nonempty (D.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N) ∧
      ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' t) (N' : T.Modules), Scheme.Modules.IsInvertible N' →
        Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N') → D'.I = D.I := by sorry
