-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ratio_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/8ed018ef-78af-523a-b5ff-e5187742f6e1
-- title:
--   Ratio of two sections of an invertible module
-- statement:
--   Let $X$ be a scheme and $M$ an $X$-module satisfying the predicate `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ on which the pullback of $M$ along the inclusion is isomorphic to the unit module $\mathcal O_U$. Let $s,t\colon \mathbb 1 \to M$ be two morphisms from the unit module, i.e. global sections of $M$. Write $Z(t)$ for `Scheme.Modules.zeroSchemeIdeal t`, the smallest ideal sheaf datum on $X$ whose ideal on each affine open $U$ contains the span of all coefficients $\mathrm{coeff}\,t\,U\,\varphi$ of $t$ taken over all morphisms $\varphi\colon M|_U \to \mathcal O_U$, and let $V$ be the open complement of the support of $Z(t)$. The assertion is that there is a section $r \in \Gamma(X,V)$ such that for every affine open $U$ of $X$ with $U \le V$ and every isomorphism $\tau\colon M|_U \xrightarrow{\ \sim\ } \mathcal O_U$, the restriction of $r$ to $U$ satisfies $r|_U \cdot \mathrm{coeff}\,t\,U\,\tau = \mathrm{coeff}\,s\,U\,\tau$ in $\Gamma(X,U)$. Here $\mathrm{coeff}\,s\,U\,\tau$ denotes the function on $U$ obtained by applying $\tau$ to the restriction of $s$ to $U$ and reading the result as an element of $\Gamma(X,U)$.
--
--   This is the elementary construction of the ratio $r = s/t$ as a regular function on the locus where $t$ generates the invertible module $M$, together with its characterisation through every local trivialisation. It is used in the construction of two-chart coverings of smooth proper curves from a section of an invertible module, in [`AlgebraicGeometry.SmoothProperCurve.exists_twoChart_of_section_invModule`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_twoChart_of_section_invModule) and its global variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ratio_section
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s t : 𝟙_ X.Modules ⟶ M) :
    ∃ r : Γ(X, (Scheme.Modules.zeroSchemeIdeal t).support.compl),
      ∀ (U : X.affineOpens) (hU : U.1 ≤ (Scheme.Modules.zeroSchemeIdeal t).support.compl)
        (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        (X.presheaf.map (homOfLE hU).op).hom r * Scheme.Modules.coeff t U.1 τ.hom =
          Scheme.Modules.coeff s U.1 τ.hom := by sorry
