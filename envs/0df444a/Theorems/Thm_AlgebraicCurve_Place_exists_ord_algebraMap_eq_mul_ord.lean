-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord
-- name    : AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/4a6afafb-d24c-5767-be5f-dfacc8bd73c8
-- title:
--   Ramification index: ord_w = ecdotordᵥ on F
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$ (no compatibility between the three structure maps, and no algebraicity or finiteness of $F'/F$, is assumed). Here a place of a field $L$ over $K$ consists of a valuation subring $\mathcal O \subseteq L$ which contains the image of $K$, is not all of $L$, and is a principal ideal ring; its order function $\operatorname{ord}$ is the negative of the logarithm of the associated adic valuation at the height-one point of $\mathcal O$, i.e. the normalised discrete valuation, with the convention $\operatorname{ord}(0)=0$. Given such a place $w$ of $F'$ over $K$, a place $v$ of $F$ over $K$, and the hypothesis that the valuation subring of $v$ is exactly the preimage of the valuation subring of $w$ under the structure map $F \to F'$ (that is, $\mathcal O_v = \mathcal O_w \cap F$, so $w$ lies over $v$), the assertion is that there exists a natural number $e$ with $e > 0$ such that for every $f \in F$ one has $\operatorname{ord}_w(\operatorname{alg}(f)) = e \cdot \operatorname{ord}_v(f)$, where $\operatorname{alg}$ denotes the map $F \to F'$.
--
--   This is the existence of the ramification index $e(w\mid v)$ of a place $w$ lying over a place $v$, in the form of proportionality of the two normalised order functions on $F$. It underpins the comparison of orders in towers of function fields, and is used for the criteria that a function with nowhere-negative order lies in the base field and for the order computations for the $j$-coordinate on the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] (w : Place K F') (v : Place K F) (hv : v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F')) : ∃ e : ℕ, 0 < e ∧ ∀ f : F, w.ord (algebraMap F F' f) = e * v.ord f := by sorry
