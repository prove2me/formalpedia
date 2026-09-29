-- Prove2me | Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
-- name    : AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/c0539457-03dc-5bba-bfee-28cd2c1e352c
-- title:
--   Degree along a map equals relative degree over its image
-- statement:
--   Let $K$ and $E$ be fields with $E$ a $K$-algebra, let $A$ and $B$ be intermediate fields of $E/K$, and let $\varphi : A \to B$ be a $K$-algebra homomorphism. The left-hand quantity [`AlgebraicCurve.finrankAlong K φ`](def/AlgebraicCurve_Correspondence.html#L51) is, by definition, the $\mathbb{N}$-valued module rank $\operatorname{finrank}_A B$ computed for the $A$-algebra structure on $B$ transported along $\varphi$, i.e. the scalar action $a \cdot b = \varphi(a) b$; as usual for `Module.finrank` this value is $0$ when $B$ is not finite-dimensional in this sense. The right-hand quantity is `IntermediateField.relfinrank` of the intermediate field $\varphi(A) \subseteq E$ — the field range of $\varphi$ followed by the inclusion $B \hookrightarrow E$ — inside $B$, that is the degree of $B$ over $\varphi(A) \sqcap B = \varphi(A)$. The assertion is that these two natural numbers agree: the degree of $B$ over $A$ along $\varphi$ equals $[B : \varphi(A)]$. No finiteness or separability hypothesis is imposed, and the base field $K$ is arbitrary.
--
--   In the function-field formulation of algebraic curves used here, a finite morphism of curves is recorded as a $K$-algebra map between function fields and its degree as `finrankAlong`; this lemma identifies that degree with Mathlib's relative degree of intermediate fields, so that degrees of maps can be computed by exhibiting the image subfield. It is the bridge used by the degree computations for modular function fields and for the specialisation and prolongation arguments on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange.lean

import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange {K E : Type*} [Field K] [Field E] [Algebra K E] (A B : IntermediateField K E) (φ : A →ₐ[K] B) : AlgebraicCurve.finrankAlong K φ = IntermediateField.relfinrank ((B.val.comp φ).fieldRange) B := by sorry
