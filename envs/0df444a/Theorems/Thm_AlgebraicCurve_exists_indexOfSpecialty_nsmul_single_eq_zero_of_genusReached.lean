-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
-- name    : AlgebraicCurve.exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/42d1d42d-658c-50e6-a41f-6d40bc7f47b4
-- title:
--   Strong approximation: i(nQ)=0 for some n
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`, i.e. every nonzero $f \in F$ has a degree-zero divisor recording its orders $\operatorname{ord}_v f$ at all places, each residue field $\kappa(v)$ of a place $v$ (a proper valuation subring of $F$ containing $K$ whose ring is a principal ideal ring) is a finite-dimensional $K$-module, and $\Omega_{F/K}$ is free of rank $1$ over $F$; assume moreover that `Place K F` is nonempty and that the space $L(0) = \{f \in F : v(f) \le 1 \text{ for all } v\}$ is finite-dimensional over $K$. Let $\gamma \in \mathbb{Z}$ and let $D_0$ be a divisor (a finitely supported $\mathbb{Z}$-valued function on places) with `RiemannGenusReachedAt γ D₀`: $L(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \mathrm{ell}(D_0) = \gamma - 1$, and $\deg D - \mathrm{ell}(D) \le \gamma - 1$ for every divisor $D$. Then for every place $Q$ there exists $n \in \mathbb{N}$ such that $\mathrm{indexOfSpecialty}(n \cdot \delta_Q) = 0$, i.e. the $K$-dimension of the quotient of the adele space by the sum of the subspaces of adeles bounded by $n\cdot\delta_Q$ and of diagonal (principal) adeles vanishes.
--
--   This is the Strong Approximation Theorem in the currency of the index of specialty: for $n$ large, $\mathcal{A}_F = \mathcal{A}_F(nQ) + F$. It feeds [`AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists`](thm.html#AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists), where combined with the index formula it shows that the genus bound is already attained at a multiple of a single place, and is also used in [`AlgebraicCurve.eq_genusFF_of_forall_ell_sub_ell_eq`](thm.html#AlgebraicCurve.eq_genusFF_of_forall_ell_sub_ell_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, indexOfSpecialty ((n : ℤ) • Finsupp.single Q (1 : ℤ)) = 0 := by sorry
