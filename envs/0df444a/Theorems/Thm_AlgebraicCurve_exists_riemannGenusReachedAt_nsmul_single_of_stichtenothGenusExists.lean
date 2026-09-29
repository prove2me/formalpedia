-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
-- name    : AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/ca093734-12dd-594a-980b-08b791760f21
-- title:
--   Genus bound attained at a multiple of any single place
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`: every nonzero $f \in F$ has a principal divisor of degree $0$ whose coefficient at each place is $\operatorname{ord}_v f$, each place has residue field finite over $K$, and the module of Kähler differentials $\Omega[F/K]$ is free of rank $1$ over $F$; here a place is a valuation subring of $F$ containing $\operatorname{im}(K)$, distinct from $F$ itself, and a principal ideal ring, and a divisor is a finitely supported function from places to $\mathbb{Z}$, with $\deg$ the sum of its coefficients weighted by the residue degrees. Assume the set of places is nonempty and that the Riemann–Roch space $\mathrm{LSpace}(0) = \{f \in F : v(f) \le 1 \text{ for all } v\}$ is finite-dimensional over $K$. Let $\gamma \in \mathbb{Z}$ and let $D_0$ be a divisor at which the Riemann genus bound $\gamma$ is reached, i.e. $\mathrm{LSpace}(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. Then for every place $Q$ there exists $n \in \mathbb{N}$ such that the bound $\gamma$ is likewise reached at the divisor $n \cdot Q$, that is, $\mathrm{LSpace}(n\,Q)$ is finite-dimensional, $\deg(n\,Q) - \ell(n\,Q) = \gamma - 1$, and the same maximality holds.
--
--   This is the form in which the strong approximation theorem for function fields enters the development: the supremum defining the genus is already attained on the divisors supported at a single prescribed place, equivalently the index of specialty of $n\,Q$ vanishes for some $n$. It is used in the computation of $\ell$ for multiples of a place and in the behaviour of the index of specialty under extension of the constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, RiemannGenusReachedAt γ ((n : ℤ) • Finsupp.single Q 1) := by sorry
