-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f2818cbd-7d7b-5f59-bef7-e05ab14e7965
-- title:
--   Zero divisor of a section has degree χ(M)-χ(𝒪)
-- statement:
--   Let $f\colon\mathcal C\to S$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically irreducible, let $k$ be a field and $x\colon\operatorname{Spec}k\to S$ a point of $S$, and work on the fibre $\mathcal C_x=\mathcal C\times_S\operatorname{Spec}k$. Let $M$ be a module on $\mathcal C_x$ that is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $M$ along $U\hookrightarrow\mathcal C_x$ is isomorphic to the unit module, and let $s\colon\mathbf 1\to M$ be a nonzero section. Let $\mathcal V$ be a cover of $\mathcal C_x$ by two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine, and let $d\in\mathbb N$. Assume the two-chart Čech Euler characteristics over $k$ (computed from $\Gamma(M,U_0)\times\Gamma(M,U_1)\to\Gamma(M,U_0\cap U_1)$, with $H^0$ its kernel and $H^1$ its cokernel, the $k$-structure coming from $\mathcal C_x\to\operatorname{Spec}k$) satisfy $\dim_k H^0(M)-\dim_k H^1(M)=\dim_k H^0(\mathbf 1)-\dim_k H^1(\mathbf 1)+d$. Then there is a relative effective Cartier divisor $D$ of degree $d$ for $f$ over $x$, that is, an ideal sheaf datum $D.I$ on $\mathcal C_x$ whose closed immersion followed by $\mathcal C_x\to\operatorname{Spec}k$ is finite, flat and locally of finite presentation with fibre rank $d$ at every point, such that $D.I$ is the zero-scheme ideal of $s$ (the infimum of those ideal sheaf data whose ideal on each affine open contains the span of the coefficients of $s$), together with an isomorphism $e\colon M\cong D.I^{\vee}$ onto the dual of the kernel defining $D.I$ for which $s$ followed by $e$ is the canonical section $D.I.\mathrm{invModuleSection}$.
--
--   This is the degree-pinned form of the statement that a nonzero section of a line bundle on a smooth proper geometrically irreducible curve over a field cuts out an effective divisor $Z(s)$ with $M\cong\mathcal O(Z(s))$, the degree being read off from Riemann–Roch as $\chi(M)-\chi(\mathcal O)$. It feeds the relative Picard machinery of the project, notably the construction of divisors supported in a prescribed closed subset and the identification of points of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq.lean

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

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0)
    (𝒱 : (pullback f x).TwoAffineOpenCover) (d : ℕ)
    (hχ : (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) M).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd f x) (𝟙_ (pullback f x).Modules)).H1 + d) :
    ∃ D : RelEffCartierDiv f d x, D.I = Scheme.Modules.zeroSchemeIdeal s ∧
      ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by sorry
