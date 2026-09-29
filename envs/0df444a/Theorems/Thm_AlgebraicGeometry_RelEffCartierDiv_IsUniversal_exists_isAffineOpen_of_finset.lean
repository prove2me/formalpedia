-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_isAffineOpen_of_finset
-- name    : AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_isAffineOpen_of_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/572d385b-e5cc-5d88-a8af-537ea85c1a8a
-- title:
--   Affine neighbourhoods of finite point sets on universal divisor schemes
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a separated morphism of schemes which is smooth of relative dimension $1$, and assume the covering hypothesis `hcov`: for every affine open $V \subseteq S$ and every finite set $F$ of points of $\mathcal{C}$ all of whose images under $f$ lie in $V$, there is an open $U \subseteq \mathcal{C}$ which is an affine open, satisfies $U \le f^{-1}V$, and contains every point of $F$. Let $r \in \mathbb{N}$, let $y \colon Y \to S$ be a morphism, and let $D_{\mathrm{univ}}$ be a `RelEffCartierDiv f r y`, that is, an ideal sheaf datum $I$ on $\mathcal{C} \times_S Y$ whose closed subscheme inclusion followed by the second projection to $Y$ is finite, flat and locally of finite presentation and has fibre rank exactly $r$ at every point of $Y$. Assume $D_{\mathrm{univ}}$ is universal: for every $g \colon T \to S$ and every such divisor datum $D$ for $g$ there is a unique morphism $\varphi \colon T \to Y$ with $\varphi$ followed by $y$ equal to $g$ and with the comap of $I$ along the induced map of products equal to $D.I$. Then, for every affine open $V \subseteq S$ and every finite set $F$ of points of $Y$ with $y(p) \in V$ for all $p \in F$, there is an open $W \subseteq Y$ which is an affine open, satisfies $W \le y^{-1}V$, and contains every point of $F$.
--
--   This is the transfer of the "AF" type covering property (finite sets of points over an affine base open admit a common affine open neighbourhood over that open) from a smooth separated relative curve $\mathcal{C}/S$ to a scheme $Y$ carrying a universal relative effective divisor of degree $r$, i.e. to $\operatorname{Div}^r_{\mathcal{C}/S}$. It is used in the construction of the relative Picard and Jacobian machinery, where affine charts of $\operatorname{Div}^r$ containing prescribed finite sets of points are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_isAffineOpen_of_finset.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_isAffineOpen_of_finset
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}
    (hU : Duniv.IsUniversal) (V : S.affineOpens) (F : Finset Y)
    (hF : ∀ p ∈ F, y p ∈ (V : S.Opens)) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ W ≤ y ⁻¹ᵁ (V : S.Opens) ∧ ∀ p ∈ F, p ∈ W := by sorry
