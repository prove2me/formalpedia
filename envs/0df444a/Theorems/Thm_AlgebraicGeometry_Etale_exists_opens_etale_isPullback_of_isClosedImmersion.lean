-- Prove2me | Theorems.Thm_AlgebraicGeometry_Etale_exists_opens_etale_isPullback_of_isClosedImmersion
-- name    : AlgebraicGeometry.Etale.exists_opens_etale_isPullback_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/8838ed22-b0cc-5440-b0a5-7dc4d388bf2d
-- title:
--   Local lifting of étale morphisms along a closed immersion
-- statement:
--   Let $X$, $X_0$, $Y_0$ be schemes (in the bottom universe), let $i : X_0 \to X$ be a closed immersion, let $q_0 : Y_0 \to X_0$ be étale, and let $y$ be a point of $Y_0$. The assertion is that there exist an open subscheme $V_0$ of $Y_0$ with $y \in V_0$, a scheme $V$, a morphism $q_V : V \to X$ which is étale, and a morphism $j_V : V_0 \to V$ (with $V_0$ regarded as a scheme via its canonical open immersion $V_0 \hookrightarrow Y_0$) such that the square with top edge $j_V$, left edge the composite of the inclusion $V_0 \hookrightarrow Y_0$ with $q_0$, right edge $q_V$ and bottom edge $i$ is a pullback square; that is, $j_V$ followed by $q_V$ equals the inclusion $V_0 \hookrightarrow Y_0$ followed by $q_0$ followed by $i$, and this commutative square exhibits $V_0$ as $V \times_X X_0$. Thus $q_0$ restricted to a neighbourhood of $y$ is the base change along $i$ of an étale morphism to $X$; the statement is purely local at $y$ and makes no claim of uniqueness or of globality over $Y_0$.
--
--   This is the local form of the classical statement that étale schemes over a closed subscheme extend, locally, to étale schemes over the ambient scheme (EGA IV 18.1, SGA 1 Exp. I). It is used by [`AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent`](thm.html#AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent), in the development of the infinitesimal lifting properties of étale morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Etale_exists_opens_etale_isPullback_of_isClosedImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Etale.exists_opens_etale_isPullback_of_isClosedImmersion
    {X X₀ Y₀ : Scheme.{0}} (i : X₀ ⟶ X) [IsClosedImmersion i] (q₀ : Y₀ ⟶ X₀) [Etale q₀] (y : Y₀) :
    ∃ (V₀ : Y₀.Opens) (_ : y ∈ V₀) (V : Scheme.{0}) (qV : V ⟶ X) (_ : Etale qV) (jV : (V₀ : Scheme.{0}) ⟶ V),
      IsPullback jV (V₀.ι ≫ q₀) qV i := by sorry
