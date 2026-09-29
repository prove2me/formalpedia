-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated
-- name    : AlgebraicGeometry.eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3e05fa09-cb6d-57ea-9b4b-1594635876c3
-- title:
--   A valuation ring dominates at most one point of a separated integral scheme
-- statement:
--   Let $X$ be an integral separated scheme (in the lowest universe), so that its function field $K(X)$, the stalk at the generic point, is defined, and let $\mathcal{O}_v \subseteq K(X)$ be a valuation subring. Let $x_1, x_2$ be points of $X$. Assume for $i = 1, 2$ that the canonical algebra map from the stalk $\mathcal{O}_{X,x_i}$ to $K(X)$ sends every element of the stalk into $\mathcal{O}_v$ (hypotheses `h₁`, `h₂`), and that it sends every element of the maximal ideal of the local ring $\mathcal{O}_{X,x_i}$ into the non-units of $\mathcal{O}_v$, i.e. into the maximal ideal of the valuation ring (hypotheses `h₁'`, `h₂'`). In other words, $\mathcal{O}_v$ dominates each of the two local rings $\mathcal{O}_{X,x_1}$ and $\mathcal{O}_{X,x_2}$ inside $K(X)$. The conclusion is that $x_1 = x_2$.
--
--   This is the uniqueness half of the valuative criterion of separatedness, read pointwise: a valuation ring of the function field can dominate at most one point of a separated integral scheme. It is used in the study of the Čerednik–Drinfeld uniformisation, where it feeds the identification of the function field of a quotient with an invariant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated
    {X : Scheme.{0}} [IsIntegral X] [X.IsSeparated]
    (𝒪v : ValuationSubring X.functionField) (x₁ x₂ : X)
    (h₁ : ∀ g : X.presheaf.stalk x₁, algebraMap (X.presheaf.stalk x₁) X.functionField g ∈ 𝒪v)
    (h₁' : ∀ g : X.presheaf.stalk x₁, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x₁) →
      algebraMap (X.presheaf.stalk x₁) X.functionField g ∈ 𝒪v.nonunits)
    (h₂ : ∀ g : X.presheaf.stalk x₂, algebraMap (X.presheaf.stalk x₂) X.functionField g ∈ 𝒪v)
    (h₂' : ∀ g : X.presheaf.stalk x₂, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x₂) →
      algebraMap (X.presheaf.stalk x₂) X.functionField g ∈ 𝒪v.nonunits) :
    x₁ = x₂ := by sorry
