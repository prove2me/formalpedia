-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/a105b32d-a287-544c-a7f8-1e4478c1b912
-- title:
--   Divisor of a section on a smooth geometrically irreducible fibre
-- statement:
--   Let $f\colon\mathcal C\to S$ be a morphism of schemes, $k$ a field and $x\colon\operatorname{Spec}k\to S$ a point of $S$, and write $\mathcal C_x=\mathcal C\times_S\operatorname{Spec}k$ with its second projection $\mathcal C_x\to\operatorname{Spec}k$; assume this projection is proper, smooth of relative dimension $1$ and geometrically irreducible (no hypothesis is placed on the other fibres of $f$). Let $M$ be a module on $\mathcal C_x$ which is invertible in the sense that every point has an open neighbourhood $U$ with the restriction of $M$ to $U$ isomorphic to the unit module, and let $s\colon\mathbf 1\to M$ be a nonzero morphism from the unit module, i.e. a global section. Let $\mathcal V$ be a cover of $\mathcal C_x$ by two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine, and let $d\in\mathbb N$. The hypothesis is the Čech Euler-characteristic equality, for the two-chart complex $\Gamma(N,U_0)\times\Gamma(N,U_1)\to\Gamma(N,U_0\cap U_1)$ attached to $\mathcal V$ and the structure morphism of $\mathcal C_x$, whose $H^0$ is the kernel and whose $H^1$ is the cokernel: $\dim_k H^0(M)-\dim_k H^1(M)=\dim_k H^0(\mathbf 1)-\dim_k H^1(\mathbf 1)+d$. The conclusion asserts the existence of a relative effective Cartier divisor $D$ of $f$ of degree $d$ over $x$, that is, an ideal sheaf datum $D.I$ on $\mathcal C_x$ whose closed subscheme inclusion followed by the projection $\mathcal C_x\to\operatorname{Spec}k$ is finite, flat and locally of finite presentation with fibre rank $d$ at every point, such that $D.I$ equals the zero-scheme ideal of $s$ (the infimum of those ideal sheaf data whose ideal on each affine open contains the span of the coefficients of $s$ there), together with an isomorphism $e\colon M\cong D.I^{-1}$, the dual of the ideal module of $D.I$, with $s$ followed by $e$ equal to the canonical section of $D.I^{-1}$.
--
--   This is the fibrewise form of the statement that a nonzero section of an invertible module on a proper smooth geometrically irreducible curve cuts out an effective divisor of degree $\chi(M)-\chi(\mathcal O)$ and identifies $M$ with $\mathcal O(Z(s))$, the hypotheses being imposed on the single fibre $\mathcal C_x$ rather than on $f$, so that it applies to families with singular fibres elsewhere. It is used in the construction of relative effective Cartier divisors from sections of line bundles on fibres in the work on the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S}
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    [IsProper (pullback.snd f x)] [SmoothOfRelativeDimension 1 (pullback.snd f x)]
    [GeometricallyIrreducible (pullback.snd f x)]
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0)
    (𝒱 : (pullback f x).TwoAffineOpenCover) (d : ℕ)
    (hχ : (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H1 + d) :
    ∃ D : RelEffCartierDiv f d x, D.I = Scheme.Modules.zeroSchemeIdeal s ∧
      ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by sorry
