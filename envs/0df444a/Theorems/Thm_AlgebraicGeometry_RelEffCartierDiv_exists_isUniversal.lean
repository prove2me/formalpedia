-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/6ff02741-dd7a-5e73-857c-d616052478f0
-- title:
--   Existence of a universal relative effective divisor of degree r
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes which is separated and smooth of relative dimension $1$, and assume the covering hypothesis $\mathrm{hcov}$: for every affine open $V$ of $S$ and every finite set $F$ of points of $\mathcal{C}$ with $f(x) \in V$ for all $x \in F$, there is an open $U \subseteq \mathcal{C}$ which is affine, satisfies $U \le f^{-1}(V)$, and contains every point of $F$. Let $r$ be a natural number. Then there exist a scheme $Y$, a morphism $y \colon Y \to S$, and a relative effective Cartier divisor $D_{\mathrm{univ}}$ of degree $r$ for $f$ over $y$ — that is, ideal sheaf data $I$ on the pullback $\mathcal{C} \times_S Y$ whose associated closed immersion, followed by the projection $\mathcal{C} \times_S Y \to Y$, is finite, flat and locally of finite presentation and has fibre rank exactly $r$ at every point of $Y$ — which is universal in the following sense: for every scheme $T$, every $g \colon T \to S$ and every such datum $D$ for $f$ of degree $r$ over $g$, there is exactly one pair consisting of a morphism $\varphi \colon T \to Y$ with $\varphi$ followed by $y$ equal to $g$ and a proof that the comap of $D_{\mathrm{univ}}$'s ideal sheaf data along the induced morphism $\mathcal{C} \times_S T \to \mathcal{C} \times_S Y$ equals that of $D$.
--
--   This is the existence of the scheme $\mathrm{Div}^r_{\mathcal{C}/S}$ of relative effective divisors of degree $r$ on a separated, smooth relative curve, stated as a universal pair rather than as an abstract representability assertion; the hypothesis $\mathrm{hcov}$ holds in particular for quasi-projective $\mathcal{C}/S$. It is the entry point for the relative Picard constructions used further on, and is cited in the construction of open charts of the relative sub-Picard presheaf and in the properness and geometric connectedness statements for the curves occurring in the modular-curve part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by sorry
