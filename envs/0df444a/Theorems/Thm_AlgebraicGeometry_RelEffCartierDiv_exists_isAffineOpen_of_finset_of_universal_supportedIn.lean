-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_isAffineOpen_of_finset_of_universal_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_isAffineOpen_of_finset_of_universal_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/4006a056-b013-5cc9-8637-c5be41b5756c
-- title:
--   Affine neighbourhoods of finite sets in a universal divisor scheme
-- statement:
--   Let $f\colon\mathcal C\to S$ be a separated morphism of schemes and let $U\subseteq\mathcal C$ be an open subscheme such that the composite $U\hookrightarrow\mathcal C\xrightarrow{f}S$ is smooth of relative dimension $1$. Assume the covering hypothesis `hcov`: for every affine open $V$ of $S$ and every finite set $F$ of points of $U$ all of whose images under $U\hookrightarrow\mathcal C\to S$ lie in $V$, there is an affine open $W$ of $U$ contained in the preimage of $V$ and containing $F$. Fix $r\in\mathbb N$, a scheme $Y$ with a morphism $y\colon Y\to S$, and a relative effective Cartier divisor $D_{\mathrm{univ}}$ of degree $r$ for $f$ over $y$, that is, an ideal sheaf datum $I$ on $\mathcal C\times_S Y$ whose associated closed subscheme is finite, flat and locally of finite presentation over $Y$ via the second projection, with fibre rank equal to $r$ at every point of $Y$; assume its support is contained in the preimage of $U$ under the first projection. Assume further that $D_{\mathrm{univ}}$ is universal among such data supported in $U$: for every $g\colon T\to S$ and every relative effective Cartier divisor $D$ of degree $r$ for $f$ over $g$ whose support lies in the preimage of $U$, there is a unique pair consisting of $\varphi\colon T\to Y$ with $\varphi\circ\, y = g$ — written $\varphi \mathbin{≫} y = g$ — such that pulling back the ideal of $D_{\mathrm{univ}}$ along the induced map $\mathcal C\times_S T\to\mathcal C\times_S Y$ gives the ideal of $D$. Then for every affine open $V$ of $S$ and every finite set $F$ of points of $Y$ lying over $V$ there is an affine open $W\subseteq Y$ with $W\subseteq y^{-1}(V)$ and $F\subseteq W$.
--
--   The statement provides the affine-neighbourhood property needed to work locally on the scheme $Y$ representing degree-$r$ relative effective divisors supported in a smooth relative curve chart $U$: finite sets of points of $Y$ lying over an affine open of the base admit a common affine open neighbourhood inside the preimage of that affine. It is used in the construction of the relative Picard group, where invertibility of the section ideal and of its pullbacks must be checked on affine opens of $Y$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_isAffineOpen_of_finset_of_universal_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv

theorem AlgebraicGeometry.RelEffCartierDiv.exists_isAffineOpen_of_finset_of_universal_supportedIn
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] (U : 𝒞.Opens)
    [SmoothOfRelativeDimension 1 (U.ι ≫ f)]
    (hcov : ∀ (V : S.affineOpens) (F : Finset ↥U), (∀ x ∈ F, (U.ι ≫ f) x ∈ (V : S.Opens)) →
      ∃ W : (↑U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ (U.ι ≫ f) ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ W)
    (r : ℕ) {Y : Scheme.{u}} (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g), D.SupportedIn U →
      ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D)
    (V : S.affineOpens) (F : Finset Y) (hF : ∀ p ∈ F, y p ∈ (V : S.Opens)) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ W ≤ y ⁻¹ᵁ (V : S.Opens) ∧ ∀ p ∈ F, p ∈ W := by sorry
