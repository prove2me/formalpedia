-- Prove2me | Theorems.Thm_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
-- name    : FormalGroup.exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/a2bf765c-aa40-56f9-b931-e51f4198ee18
-- title:
--   Drinfeld basis of level q from q² distinct roots of [q]
-- statement:
--   Let $q$ be a prime and let $V$ be a local commutative domain which is complete and separated for the $\mathfrak m_V$-adic topology, $\mathfrak m_V =$ `maximalIdeal V`. Let $G$ be a one-dimensional commutative formal group law over $V$, and write `G.nthSeries n` for the $n$-fold iterate defined by `G.nthSeries 0 = 0` and `G.nthSeries (n+1)` = the substitution of the pair `(G.nthSeries n, X)` into the group law of $G$, i.e. the multiplication-by-$n$ series $[n]_G$. Assume given a family $r : \mathrm{Fin}(q\cdot q) \to V$ of pairwise distinct elements ($r$ injective), all lying in $\mathfrak m_V$, and a unit $U$ of $V[[X]]$, such that $$[q]_G = \Bigl(\prod_{i} (X - r_i)\Bigr)\cdot U$$ in $V[[X]]$, the product being the monic polynomial of degree $q^2$ with roots $r_i$, viewed as a power series. The conclusion is that there exist $\alpha, \beta \in \mathfrak m_V$ with `G.IsDrinfeldBasisAdic (maximalIdeal V) q α β`, that is: taking $\mathfrak m_V$ as the ideal defining the topology on $V$, there is a unit $u$ of $V[[X]]$ with $[q]_G = u \cdot$ `G.drinfeldDivisor q α β`, the Drinfeld divisor attached to the pair $(\alpha,\beta)$.
--
--   This is the statement that a $q$-divisible situation in which the multiplication-by-$q$ series of a formal group over a complete local domain splits, up to a unit, into $q^2$ distinct linear factors with roots in the maximal ideal admits a Drinfeld basis of level $q$: the $q^2$ roots form a group isomorphic to $(\mathbb Z/q)^2$ under the formal group addition, and any basis of it gives the divisor. It is used by [`FormalGroup.IsDrinfeldBasisAdic.exists_isDomain_injective_isDrinfeldBasisAdic`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_isDomain_injective_isDrinfeldBasisAdic) in the construction of level structures on formal groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
    (q : ℕ) [Fact q.Prime]
    {V : Type*} [CommRing V] [IsDomain V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (G : FormalGroup V) [G.IsComm]
    (r : Fin (q * q) → V) (hr : ∀ i, r i ∈ maximalIdeal V) (hinj : Function.Injective r)
    (U : PowerSeries V) (hU : IsUnit U)
    (hq : G.nthSeries q = ((∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial V) : PowerSeries V) * U) :
    ∃ α β : V, α ∈ maximalIdeal V ∧ β ∈ maximalIdeal V ∧ G.IsDrinfeldBasisAdic (maximalIdeal V) q α β := by sorry
