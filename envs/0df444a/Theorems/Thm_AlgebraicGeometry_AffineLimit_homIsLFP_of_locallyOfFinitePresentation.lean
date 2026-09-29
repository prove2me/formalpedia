-- Prove2me | Theorems.Thm_AlgebraicGeometry_AffineLimit_homIsLFP_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.AffineLimit.homIsLFP_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f9d9afc2-472d-5063-abd8-7499becce2b8
-- title:
--   Morphisms to a finitely presented R-scheme and f.g. subalgebras
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\xi \colon X \to \operatorname{Spec} R$ a morphism that is locally of finite presentation. The conclusion `HomIsLFP ξ` is the conjunction of two assertions. First (existence of a factorisation): for every $R$-algebra $A$ and every morphism $\varphi \colon \operatorname{Spec} A \to X$ whose composite $\varphi$ followed by $\xi$ is $\operatorname{Spec}$ of the structure map $R \to A$, there are an $R$-subalgebra $A_0 \subseteq A$ that is finitely generated and a morphism $\varphi_0 \colon \operatorname{Spec} A_0 \to X$ with $\varphi_0$ followed by $\xi$ equal to $\operatorname{Spec}$ of $R \to A_0$, such that $\operatorname{Spec}$ of the inclusion $A_0 \hookrightarrow A$ followed by $\varphi_0$ is $\varphi$. Second (essential uniqueness): for every $R$-algebra $A$, every finitely generated $R$-subalgebra $A_0 \subseteq A$ and every pair of morphisms $\varphi_0, \varphi_0' \colon \operatorname{Spec} A_0 \to X$ over $\operatorname{Spec} R$ (each composed with $\xi$ being $\operatorname{Spec}$ of $R \to A_0$) whose pullbacks along $\operatorname{Spec} A \to \operatorname{Spec} A_0$ coincide, there is a finitely generated $R$-subalgebra $A_1$ with $A_0 \le A_1 \subseteq A$ such that $\varphi_0$ and $\varphi_0'$ already agree after composing with $\operatorname{Spec}$ of the inclusion $A_1 \hookrightarrow A_0$'s overalgebra, i.e. of $A_0 \hookrightarrow A_1$.
--
--   This is the special case, for the cofiltered limit $\operatorname{Spec} A = \varprojlim_{A_0} \operatorname{Spec} A_0$ over the finitely generated $R$-subalgebras of $A$, of the statement that morphisms into a scheme locally of finite presentation over the base commute with such limits (EGA IV 8.14.2): the set of $R$-morphisms $\operatorname{Spec} A \to X$ is the filtered colimit of the sets of $R$-morphisms $\operatorname{Spec} A_0 \to X$. It is used in the construction of open charts for the relative sub-Picard presheaf, where points of a relative Picard functor over a large algebra must be spread out over a finitely generated subalgebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_AffineLimit_homIsLFP_of_locallyOfFinitePresentation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_AffineLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.AffineLimit

theorem AlgebraicGeometry.AffineLimit.homIsLFP_of_locallyOfFinitePresentation
    (R : Type u) [CommRing R] {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ξ] : HomIsLFP ξ := by sorry
