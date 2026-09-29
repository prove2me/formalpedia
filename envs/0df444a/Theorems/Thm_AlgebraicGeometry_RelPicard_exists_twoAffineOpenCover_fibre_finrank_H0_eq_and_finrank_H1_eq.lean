-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
-- name    : AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/6903d10e-0b9c-5825-ac68-96b274106dd4
-- title:
--   Field-extension invariance of two-chart Čech dimensions on fibres
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ and $t \colon T \to \operatorname{Spec} R$ be schemes over $R$, let $k$ be a field and $s \colon \operatorname{Spec} k \to T$ a $k$-valued point of $T$, and write $X_s = (C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ for the fibre, formed as the pullback of the second projection $C \times_{\operatorname{Spec} R} T \to T$ along $s$, with structure map `fibreAt c t s` to $\operatorname{Spec} k$ given by the second projection. Let $\mathcal W$ be a two-affine open cover of $X_s$, that is, two open subschemes $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ such that $U_0$, $U_1$ and $U_0 \sqcap U_1$ are affine opens. Let $K$ be a field with a $k$-algebra structure, and let $s_K$ be $\operatorname{Spec} K \to \operatorname{Spec} k$ (induced by $k \to K$) followed by $s$. The assertion is that there exists a two-affine open cover $\mathcal W'$ of the fibre $X_{s_K}$ over $\operatorname{Spec} K$, chosen once and for all, such that for every sheaf of modules $F$ on $C \times_{\operatorname{Spec} R} T$ that is invertible in the sense that every point has an open neighbourhood $U$ on which the pullback of $F$ is isomorphic to the unit sheaf of modules of $U$, one has $\dim_K H^0 = \dim_k H^0$ and $\dim_K H^1 = \dim_k H^1$, where for a two-affine cover $\mathcal V$ of a scheme $X$ with structure map to a base and a module $M$ the groups are those of the two-chart Čech complex with terms $\Gamma(M, \mathcal V.U_0)$, $\Gamma(M, \mathcal V.U_1)$, $\Gamma(M, \mathcal V.U_0 \sqcap \mathcal V.U_1)$ and differential $(m_0, m_1) \mapsto m_1|_{U_0 \cap U_1} - m_0|_{U_0 \cap U_1}$, namely $H^0$ its kernel and $H^1$ the cokernel; here the modules taken are the pullbacks of $F$ to $X_s$ and to $X_{s_K}$ along the first projections, the dimensions are `Module.finrank` over $k$ and $K$ respectively, and no finiteness or properness hypothesis on $c$, $t$ or $R$ is imposed.
--
--   This is the invariance of $h^0$ and $h^1$ of the fibres of an invertible module on a relative curve under extension of the field-valued base point, in the two-chart Čech model of cohomology, strengthened so that a single cover of the extended fibre works simultaneously for all invertible modules — the shape needed when the Euler characteristics $\chi(F_s)$ and $\chi(\mathcal O_{X_s})$ are to be compared on one cover. It feeds the study of the relative Picard presheaf, being used in [`AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut`](thm.html#AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (K : Type u) [Field K] [Algebra k K] :
    ∃ 𝒲' : (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      ∀ (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F →
        Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
            (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H0 =
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 ∧
        Module.finrank K (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
            (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) F)).H1 =
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 := by sorry
