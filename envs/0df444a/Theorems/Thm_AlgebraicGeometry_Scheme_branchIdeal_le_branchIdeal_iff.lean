-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_branchIdeal_le_branchIdeal_iff
-- name    : AlgebraicGeometry.Scheme.branchIdeal_le_branchIdeal_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/ef7ef766-c5f9-52b8-b446-b107a4820b82
-- title:
--   Branch ideals at x order-reverse specialisation of generisations
-- statement:
--   Let $X$ be a scheme (in universe `v`) and let $a$, $b$, $x$ be points of $X$ together with specialisations $ha : a \rightsquigarrow x$ and $hb : b \rightsquigarrow x$, so that both $a$ and $b$ are generisations of $x$. For such data the project's `Scheme.branchIdeal` attached to a specialisation $\xi \rightsquigarrow x$ is the ideal of the stalk $\mathcal{O}_{X,x}$ obtained by pulling back the maximal ideal of $\mathcal{O}_{X,\xi}$ along the ring map $\mathcal{O}_{X,x} \to \mathcal{O}_{X,\xi}$ induced by the specialisation (`stalkSpecializes`); thus $\mathrm{branchIdeal}\,ha$ and $\mathrm{branchIdeal}\,hb$ are ideals of $\mathcal{O}_{X,x}$. The theorem asserts the equivalence of the two assertions: the inclusion $\mathrm{branchIdeal}\,hb \subseteq \mathrm{branchIdeal}\,ha$ of ideals of $\mathcal{O}_{X,x}$, and the specialisation $b \rightsquigarrow a$ in the topological space of $X$. In other words, the passage from a generisation of $x$ to its branch ideal in the local ring at $x$ is an order-reversing dictionary between generisations of $x$ and the corresponding primes of $\mathcal{O}_{X,x}$.
--
--   This is the scheme-theoretic form of the standard correspondence between the points of $\operatorname{Spec}\mathcal{O}_{X,x}$ and the generisations of $x$ in $X$, which reverses the specialisation order. It is used in the analysis of the local structure of the Deligne–Rapoport models at a point of the special fibre, in particular by the results identifying a point whose stalk has Krull dimension at most one as a generic point of a component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_branchIdeal_le_branchIdeal_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v

theorem AlgebraicGeometry.Scheme.branchIdeal_le_branchIdeal_iff {X : Scheme.{v}} {a b x : X} (ha : a ⤳ x) (hb : b ⤳ x) :
    Scheme.branchIdeal hb ≤ Scheme.branchIdeal ha ↔ b ⤳ a := by sorry
