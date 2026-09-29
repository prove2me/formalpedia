-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/5202cae0-ac36-5275-9bb8-fe208f22a5b8
-- title:
--   Closedness of the locus where fibrewise h¹ is at least n
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c\colon C\to\operatorname{Spec}R$ be a proper flat morphism of schemes, and assume $C$ carries a `TwoAffineOpenCover` $\mathcal V$, i.e. two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine. Let $t\colon T\to\operatorname{Spec}R$ be locally of finite type, let $M$ be a module on the fibre product $C\times_{\operatorname{Spec}R}T$ which is invertible in the sense that every point has an open neighbourhood $U$ over which the pullback of $M$ along $U\hookrightarrow C\times_R T$ is isomorphic to the unit sheaf of modules, and let $n\in\mathbb N$. The assertion is that the following subset of $T$ is closed: the set of $x\in T$ such that for every field $k$, every morphism $s\colon\operatorname{Spec}k\to T$ carrying the closed point of $\operatorname{Spec}k$ to $x$, and every two-affine open cover $\mathcal W$ of the fibre $(C\times_R T)\times_T\operatorname{Spec}k$, one has $n\le\dim_k$ of the $k$-vector space $(\mathcal W.\mathtt{sectionsOf}\dots).H1$, namely the cokernel of the Čech differential $(m_0,m_1)\mapsto -r_0m_0+r_1m_1$ from $\Gamma(M_s,W_0)\oplus\Gamma(M_s,W_1)$ to $\Gamma(M_s,W_0\cap W_1)$, where $M_s$ is the pullback of $M$ to the fibre and the $k$-structure comes from the fibre's structure morphism $\mathtt{fibreAt}$, the second projection to $\operatorname{Spec}k$.
--
--   This is the Čech-theoretic form of the upper semicontinuity of $h^1$ for an invertible module in a proper flat family over a Noetherian base (EGA III 7.7.5, Hartshorne III.12.8), phrased as closedness of the locus where the fibrewise first cohomology has dimension at least $n$, uniformly over all field points above a given point and all two-affine covers of the fibre. It feeds the identification of the locus in the base on which fibres of the relative Picard construction are algebraically equivalent to zero, for families of two glued smooth curve degenerations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover.lean

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

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isClosed_setOf_forall_fibre_le_finrank_H1_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          n ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1} := by sorry
