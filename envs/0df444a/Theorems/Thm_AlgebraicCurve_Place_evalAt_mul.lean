-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
-- name    : AlgebraicCurve.Place.evalAt_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/7f4b84de-8c77-5726-b122-34154855c5c6
-- title:
--   Evaluation at a rational place is multiplicative
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Write $\kappa(v)$ for the residue field of the local ring $\mathcal O_v$, and let $\mathrm{ev}_v \colon F \to K$ be the evaluation map that sends $f$ to the image of the residue class of $f$ under a fixed set-theoretic inverse of the structure map $K \to \kappa(v)$ when $f \in \mathcal O_v$, and to $0$ otherwise. Assume $v$ is rational, meaning that the map $K \to \kappa(v)$ is surjective, so that this inverse is a genuine section. Then for all $f, g \in F$ lying in $\mathcal O_v$ one has $\mathrm{ev}_v(fg) = \mathrm{ev}_v(f)\,\mathrm{ev}_v(g)$ in $K$. (No hypothesis is placed on $fg$ beyond what follows from $f, g \in \mathcal O_v$.)
--
--   This is the multiplicativity of the evaluation-at-a-place map $f \mapsto f(v)$ on functions regular at $v$, i.e. the statement that evaluation is the composite of the residue homomorphism $\mathcal O_v \to \kappa(v)$ with the inverse of the identification $\kappa(v) \cong K$ furnished by rationality of $v$. It belongs to the function-field layer underlying the theory of divisors, Weil reciprocity and the Weil pairing on modular curves, and is used throughout the computations with functions on annuli and charts in that layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_mul.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_mul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) : v.evalAt (f * g) = v.evalAt f * v.evalAt g := by sorry
