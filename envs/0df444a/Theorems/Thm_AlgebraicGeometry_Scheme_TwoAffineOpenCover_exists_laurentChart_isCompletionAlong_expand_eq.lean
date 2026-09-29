-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_expand_eq
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_expand_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/858389b7-f43d-5e6d-8262-484ae590bd3d
-- title:
--   Laurent chart along a section with prescribed parameter t₀
-- statement:
--   Let $R$ be a commutative local ring and $X$ a scheme, let $\mathcal{V}$ be a two-affine open cover of $X$, i.e. affine opens $U_0,U_1$ with $U_0\cup U_1=X$ and $U_0\cap U_1$ affine, and let $c\colon X\to\operatorname{Spec}R$ be smooth of relative dimension $1$. Let $\sigma\colon\iota\to\operatorname{Hom}(\operatorname{Spec}R,X)$ be a family which is sectional for $c$ and $\mathcal{V}$: each $\sigma_j$ followed by $c$ is the identity, each image lies in $U_0$, the complement of $U_1$ is the union of the images, and the images are pairwise disjoint. Fix $j=i$ and write $e$ for the induced $R$-algebra map $\Gamma(X,U_0)\to R$ given by pulling back along $\sigma_i$. Let $t_0\in\Gamma(X,U_0)$ satisfy $e(t_0)=0$ and $\ker e\le (t_0)+(\ker e)^2$. Then there is a Laurent chart $\Lambda$ for the cover, that is a ring homomorphism $\mathrm{expand}\colon\Gamma(X,U_0\cap U_1)\to R((t))$ carrying $r\in R$ to the constant series $r$, which is a completion along the restriction $\rho_0\colon\Gamma(X,U_0)\to\Gamma(X,U_0\cap U_1)$ and $e$, namely: $\mathrm{expand}(\rho_0 a)$ is a power series for every $a$; for every $n$ and every $p\in R[[t]]$ some $a$ has $\mathrm{expand}(\rho_0 a)$ agreeing with $p$ in all coefficients of degree $<n$; and the coefficients of $\mathrm{expand}(\rho_0 a)$ in degrees $<n$ all vanish exactly when $a\in(\ker e)^n$. Moreover $\mathrm{expand}(\rho_0 t_0)=t$, the Hahn series with single coefficient $1$ in degree $1$.
--
--   This is the formal expansion of functions along a boundary section of a smooth relative curve, realised as an isomorphism $\Gamma(U_0,\mathcal{O}_X)/(\ker e)^n\cong R[[t]]/(t^n)$ for all $n$, strengthened so that a prescribed local parameter $t_0$ along the section expands to the coordinate $t$ itself. It feeds the construction of Laurent charts with a distinguished parameter used in the Serre-duality pairing for smooth proper curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_expand_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_expand_eq {R : Type u} [CommRing R] [IsLocalRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of R))
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c]
    {ι : Type v} (σ : ι → (AlgebraicGeometry.Spec (.of R) ⟶ X)) (h : 𝒱.IsSectional c σ) (i : ι)
    (t₀ : (𝒱.cover c).A0) (ht₀ : AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i) t₀ = 0)
    (hgen : RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ≤
      Ideal.span {t₀} ⊔ RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ^ 2) :
    ∃ Λ : (𝒱.cover c).LaurentChart,
      Λ.IsCompletionAlong (𝒱.cover c).ρ0 (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)) ∧
        Λ.expand ((𝒱.cover c).ρ0 t₀) = HahnSeries.single 1 1 := by sorry
