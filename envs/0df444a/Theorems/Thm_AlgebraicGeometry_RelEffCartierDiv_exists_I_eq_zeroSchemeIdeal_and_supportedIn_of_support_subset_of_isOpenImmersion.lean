-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/554a52a2-1572-5655-925e-c8fe7505d279
-- title:
--   Zero scheme of a section as relative effective Cartier divisor
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes, $U$ an open subscheme of $C$, $k$ a field and $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$; write $X$ for the fibre product of $c$ and $x$. Let $y\colon Y\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically irreducible, and let $i\colon Y\to X$ satisfy $i$ followed by the second projection $=y$. Let $W_1\subseteq X$ be open such that the inclusion of $i^{-1}W_1$ followed by $i$ is an open immersion, with $W_1$ contained in the set-theoretic image of $i$ and $W_1\le \mathrm{pr}_1^{-1}U$. Let $M$ be a module on $X$ that is invertible, in the sense that every point has an open neighbourhood $V$ with $M|_V$ isomorphic to the unit module, and let $\sigma$ be a map from the unit module to $M$ whose zero-scheme ideal sheaf data $\mathcal I(\sigma)$ — the infimum of all ideal sheaf data $J$ with, on every affine open $V$, the ideal of $\Gamma(X,V)$ spanned by the coefficients of $\sigma$ contained in $J(V)$ — has support contained in $W_1$, and whose pullback section along $i$ is nonzero. Let $g\in\mathbb N$ and let $\mathcal V$ be a cover of $Y$ by two affine opens with affine intersection, and assume the two-chart Čech Euler characteristics over $y$ satisfy $\dim_k H^0(\mathcal V,i^*M)-\dim_k H^1(\mathcal V,i^*M)=\dim_k H^0(\mathcal V,\mathcal O_Y)-\dim_k H^1(\mathcal V,\mathcal O_Y)+g$. Then there exists a relative effective Cartier divisor $D$ of degree $g$ on $X$ over $\operatorname{Spec}k$ — ideal sheaf data on $X$ whose closed subscheme, mapped by the second projection, is finite, flat and locally of finite presentation with fibre rank $g$ at every point of $\operatorname{Spec}k$ — such that $D.I=\mathcal I(\sigma)$ and the support of $D.I$ is contained in $\mathrm{pr}_1^{-1}U$.
--
--   This is the transport statement that the divisor of a section of an invertible module, when its zero scheme is supported in an open piece isomorphic to an open part of a smooth proper geometrically irreducible curve, is a relative effective Cartier divisor of the degree read off from the Euler characteristic on that curve, and is supported over the prescribed open $U$ of $C$. It feeds the construction of divisors on two glued projective lines used in the study of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] [SmoothOfRelativeDimension 1 y] [GeometricallyIrreducible y]
    (i : Y ⟶ pullback c x) (hi : i ≫ pullback.snd c x = y)
    (W₁ : (pullback c x).Opens) [IsOpenImmersion ((i ⁻¹ᵁ W₁).ι ≫ i)]
    (hW₁ : (W₁ : Set ↥(pullback c x)) ⊆ Set.range i.base)
    (hWU : W₁ ≤ (pullback.fst c x) ⁻¹ᵁ U)

    (M : (pullback c x).Modules) (hM : Scheme.Modules.IsInvertible M)
    (σ : 𝟙_ (pullback c x).Modules ⟶ M)
    (hsupp : ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c x)) ⊆ (W₁ : Set ↥(pullback c x)))
    (hσ : Scheme.Modules.pullbackSection i σ ≠ 0)

    (g : ℕ) (𝒱 : Y.TwoAffineOpenCover)
    (hχ : (Module.finrank k (𝒱.sectionsOf y ((Scheme.Modules.pullback i).obj M)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf y ((Scheme.Modules.pullback i).obj M)).H1
      = (Module.finrank k (𝒱.sectionsOf y (𝟙_ Y.Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf y (𝟙_ Y.Modules)).H1 + g) :
    ∃ D : RelEffCartierDiv c g x, D.I = Scheme.Modules.zeroSchemeIdeal σ ∧ D.SupportedIn U := by sorry
