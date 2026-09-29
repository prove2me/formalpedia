-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_universal_of_smooth_opens
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_universal_of_smooth_opens
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/1f594b12-7a9a-5c7c-b4eb-4da9c0653f93
-- title:
--   Representability of degree-r divisors supported in a smooth open
-- statement:
--   Let $f\colon\mathcal C\to S$ be a separated morphism of schemes and let $U$ be an open subscheme of $\mathcal C$ such that the composite $U\hookrightarrow\mathcal C\xrightarrow{f}S$ is smooth of relative dimension $1$. Assume further the affine-neighbourhood hypothesis: for every affine open $V\subseteq S$ and every finite set $F$ of points of $U$ all of whose images under $U\hookrightarrow\mathcal C\to S$ lie in $V$, there is an open $W$ of the scheme $U$ which is affine, is contained in the preimage of $V$, and contains every point of $F$. Let $r\in\mathbb N$. Then there exist a scheme $Y$, a morphism $y\colon Y\to S$ and a relative effective Cartier divisor $\mathcal D$ of degree $r$ for $f$ over $y$ — that is, an ideal sheaf datum on $\mathcal C\times_S Y$ whose associated closed subscheme maps to $Y$ by a morphism that is finite, flat and locally of finite presentation with fibre rank exactly $r$ at every point of $Y$ — such that the support of $\mathcal D$ is contained in the preimage of $U$ under the first projection, and such that for every $g\colon T\to S$ and every degree-$r$ relative effective Cartier divisor $D$ for $f$ over $g$ whose support lies in the preimage of $U$, there is exactly one morphism $\varphi\colon T\to Y$ with $\varphi$ followed by $y$ equal to $g$ for which the comap of the ideal of $\mathcal D$ along the induced map $\mathcal C\times_S T\to\mathcal C\times_S Y$ equals the ideal of $D$.
--
--   This is the representability of the subfunctor $\mathrm{Div}^r_{\mathcal C/S,\subseteq U}$ of degree-$r$ relative effective divisors supported in the smooth open $U$, stated as unique existence of a classifying $S$-morphism rather than through the project's `IsUniversal` structure. It feeds the construction of relative Picard data for curves with two degenerate components, being cited by the two `AlgebraicGeometry.RelPicard` results on representing relative sub-Picard functors away from the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_universal_of_smooth_opens.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelEffCartierDiv

theorem AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_universal_of_smooth_opens
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] (U : 𝒞.Opens)
    [SmoothOfRelativeDimension 1 (U.ι ≫ f)]
    (hcov : ∀ (V : S.affineOpens) (F : Finset ↥U), (∀ x ∈ F, (U.ι ≫ f) x ∈ (V : S.Opens)) →
      ∃ W : (↑U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ (U.ι ≫ f) ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ W)
    (r : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.SupportedIn U ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D := by sorry
