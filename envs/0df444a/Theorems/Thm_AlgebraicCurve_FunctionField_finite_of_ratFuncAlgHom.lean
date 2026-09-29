-- Prove2me | Theorems.Thm_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom
-- name    : AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/d2a22f80-1723-5305-976b-9ae99ab56e35
-- title:
--   Finiteness of a function field over K(g) for any embedding
-- statement:
--   Let $K$ and $F$ be fields, with $F$ carrying both a $K$-algebra structure and a $(\mathrm{RatFunc}\,K)$-algebra structure that are compatible (the scalar tower condition over $K$, $\mathrm{RatFunc}\,K$, $F$), and assume that $F$ is finite-dimensional over the rational function field $\mathrm{RatFunc}\,K$ for this ambient structure. Let $\varphi : \mathrm{RatFunc}\,K \to F$ be an arbitrary homomorphism of $K$-algebras; concretely, $\varphi$ is determined by the element $g = \varphi(t) \in F$, necessarily transcendental over $K$, and $\varphi$ identifies $\mathrm{RatFunc}\,K$ with the subfield $K(g) \subseteq F$. The conclusion is that $F$ is a finite module over $\mathrm{RatFunc}\,K$ for the module structure obtained by restricting scalars along $\varphi$, rather than for the ambient one: the $\mathrm{RatFunc}\,K$-algebra structure on $F$ coming from the ring homomorphism underlying $\varphi$ makes $F$ a finitely generated $\mathrm{RatFunc}\,K$-module, i.e. $[F : K(g)] < \infty$. The two $(\mathrm{RatFunc}\,K)$-module structures on $F$, the given one and the one induced by $\varphi$, are in general different, and the statement transfers finiteness from the former to the latter.
--
--   This is the standard rebasing finiteness for one-variable function fields: a field finite over $K(t)$ is finite over $K(g)$ for every non-constant $g$, since it has transcendence degree one over $K$ and is finitely generated. It is used in the proofs of Weil reciprocity, [`AlgebraicCurve.weilReciprocity`](thm.html#AlgebraicCurve.weilReciprocity) and [`AlgebraicCurve.weilReciprocity_of_isAlgClosed`](thm.html#AlgebraicCurve.weilReciprocity_of_isAlgClosed), where reciprocity for two functions $f, g$ is reduced to the finite map determined by $g$ by taking $K(g)$ as the new base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] (φ : RatFunc K →ₐ[K] F) : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule := by sorry
