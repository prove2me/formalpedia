-- Prove2me | Theorems.Thm_FormalGroup_evalSeries_nthSeries
-- name    : FormalGroup.evalSeries_nthSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/4d643338-3491-5e6b-ba88-e90cc7a2fc57
-- title:
--   Evaluating the n-series at a topologically nilpotent point
-- statement:
--   Let $R$ be a commutative ring and let $A$ be a commutative ring carrying a uniform structure and an $R$-algebra structure, assumed to be a uniform additive group, complete, Hausdorff, a topological ring, and linearly topologised over itself (so that its topology has a basis of ideals). Let $F$ be an element of `FormalGroup R`, with underlying two-variable power series `F.toPowerSeries`, let $x \in A$ be topologically nilpotent (its powers tend to $0$), and let $n$ be a natural number. The assertion is that $\mathrm{evalSeries}(F.nthSeries\ n)\,x = F.evalNSMul\ n\ x$, where: `F.nthSeries` is the sequence of one-variable power series over $R$ defined by $0$ at $n = 0$ and, at $n+1$, by substituting the pair $(F.nthSeries\ n, X)$ into `F.toPowerSeries`; `evalSeries f x` is $\mathrm{eval}_2$ of $f$ along `algebraMap R A` at the point $x$, with $R$ given the discrete uniformity; and `F.evalNSMul` is defined by $0$ at $n = 0$ and, at $n+1$, by $F.eval\,(F.evalNSMul\ n\ x)\ x$, where $F.eval\ u\ v$ is the two-variable $\mathrm{eval}_2$ of `F.toPowerSeries` along `algebraMap R A` at the pair $(u,v)$. Thus the $n$-series of $F$, evaluated at $x$, equals the $n$-fold $F$-sum of $x$ with itself formed by iterating the evaluated group law.
--
--   This is the bridge from power-series identities about the multiplication-by-$n$ series $[n]$ of a formal group to identities about topologically nilpotent points of a complete linearly topologised algebra. It is used in the treatment of Drinfeld-type bases for formal groups, in particular by [`FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete), [`FormalGroup.exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective`](thm.html#FormalGroup.exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective) and [`FormalGroup.linCombAdic_map_X_eq_nthSeries`](thm.html#FormalGroup.linCombAdic_map_X_eq_nthSeries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_evalSeries_nthSeries.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FormalGroup.evalSeries_nthSeries {R : Type*} [CommRing R] {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]
    [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A]
    (F : FormalGroup R) {x : A} (hx : IsTopologicallyNilpotent x) (n : ℕ) :
    FormalGroup.evalSeries (F.nthSeries n) x = F.evalNSMul n x := by sorry
