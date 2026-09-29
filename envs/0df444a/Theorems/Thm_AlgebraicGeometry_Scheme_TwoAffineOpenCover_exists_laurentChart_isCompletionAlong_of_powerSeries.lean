-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_of_powerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/4c5af9ad-594e-5f4a-b083-f30a3cb18f43
-- title:
--   Laurent chart from a power-series expansion along a section
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\mathcal V$ a two-affine open cover of $X$: open subsets $U_0,U_1$ with $U_0,U_1$ and $U_0\cap U_1$ affine and $U_0\cup U_1=X$. Let $c:X\to\operatorname{Spec}R$ be a morphism, which makes each $\Gamma(X,U)$ an $R$-algebra, and write $\mathcal U=\mathcal V.\mathrm{cover}\,c$ for the associated cover datum with $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\cap U_1)$ and $\rho_0,\rho_1$ the restriction maps. Let $\sigma:\iota\to(\operatorname{Spec}R\to X)$ be a family which is sectional for $c$, i.e. each $\sigma_j$ satisfies $\sigma_j$ followed by $c$ is the identity, has topological image inside $U_0$, the images are pairwise disjoint, and their union is the complement of $U_1$. Fix $i\in\iota$ and let $e_i:A_0\to R$ be the $R$-algebra map `sectionAlgHom` given by pullback along $\sigma_i$, with $I=\ker e_i$. Let $\theta:A_0\to R[[t]]$ be a ring homomorphism such that $\theta(r)=C(r)$ for $r$ in the image of $R$, such that for every $n$ and $a\in A_0$ the coefficients of $\theta(a)$ in degrees $<n$ all vanish exactly when $a\in I^n$, and such that every power series is matched by some $\theta(a)$ in all degrees $<n$, for every $n$. Then there exists a Laurent chart $\Lambda$ on $\mathcal U$, that is a ring homomorphism $\Lambda.\mathrm{expand}:A_{01}\to R((t))$ sending the image of $r\in R$ to the constant Hahn series $C(r)$, such that $\Lambda.\mathrm{expand}(\rho_0 a)$ is the Laurent series attached to $\theta(a)$ for all $a\in A_0$, and such that $\Lambda$ is a completion along $(\rho_0,e_i)$: $\Lambda.\mathrm{expand}\circ\rho_0$ takes values in power series, every power series is approximated to any finite order by some $\Lambda.\mathrm{expand}(\rho_0 a)$, and for all $n$ and $a$ the non-negative coefficients of $\Lambda.\mathrm{expand}(\rho_0 a)$ in degrees $<n$ vanish exactly when $a\in I^n$.
--
--   This is the geometric input that turns a formal expansion of functions along one boundary section into a Laurent expansion on the punctured neighbourhood, the algebraic counterpart of $q$-expansion at a cusp for a two-chart cover of a modular curve. It is used by [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_expand_eq`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_expand_eq), where the chart produced here is recorded together with its prescribed values on the image of $A_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_of_powerSeries {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ AlgebraicGeometry.Spec (.of R))
    {ι : Type v} (σ : ι → (AlgebraicGeometry.Spec (.of R) ⟶ X)) (h : 𝒱.IsSectional c σ) (i : ι)
    (θ : (𝒱.cover c).A0 →+* PowerSeries R) (hθC : ∀ r : R, θ (algebraMap R (𝒱.cover c).A0 r) = PowerSeries.C r)
    (hθ0 : ∀ (n : ℕ) (a : (𝒱.cover c).A0), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
      a ∈ RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom
        (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ^ n)
    (hθs : ∀ (n : ℕ) (p : PowerSeries R), ∃ a : (𝒱.cover c).A0, ∀ k : ℕ, k < n →
      PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) :
    ∃ Λ : (𝒱.cover c).LaurentChart,
      (∀ a : (𝒱.cover c).A0, Λ.expand ((𝒱.cover c).ρ0 a) = HahnSeries.ofPowerSeries ℤ R (θ a)) ∧
        Λ.IsCompletionAlong (𝒱.cover c).ρ0
          (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)) := by sorry
