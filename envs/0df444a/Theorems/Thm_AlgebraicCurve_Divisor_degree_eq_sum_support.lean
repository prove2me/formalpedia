-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
-- name    : AlgebraicCurve.Divisor.degree_eq_sum_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/7b62f3d0-961d-566a-9c60-2ccdda7f0bd5
-- title:
--   Degree of a divisor as a sum over its support
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $D$ be a divisor of $F/K$, i.e. a finitely supported function $D \colon \mathrm{Place}\,K\,F \to \mathbb{Z}$, where a place $v$ of $F/K$ is by definition a valuation subring $v$ of $F$ that contains $\mathrm{algebraMap}\,K\,F(a)$ for every $a \in K$, is not the whole of $F$, and is a principal ideal ring. For such a place, $v.\mathrm{deg}$ is the $K$-dimension $\mathrm{finrank}_K$ of the residue field of the local ring $v$, and $\mathrm{Divisor.degree}$ is the additive homomorphism from divisors to $\mathbb{Z}$ obtained by lifting, place by place, the map 'multiply on the right by $(v.\mathrm{deg} : \mathbb{Z})$'. The theorem asserts that this homomorphism is computed by the expected finite sum: $$\mathrm{degree}\,D = \sum_{v \in \mathrm{supp}\,D} D(v)\cdot (v.\mathrm{deg} : \mathbb{Z}),$$ the sum being taken over the (finite) support of $D$ inside the type of places, with the natural number $v.\mathrm{deg}$ cast to $\mathbb{Z}$. No further hypotheses (finiteness of residue degrees, curve conditions, separability) are imposed.
--
--   This is the unfolding of the divisor degree map of a function field $F/K$ into the classical formula $\deg D = \sum_v n_v\,[\kappa(v):K]$, and it is the computational entry point for all sign arguments about degrees: it is used to show that effective divisors have non-negative degree, whence that the Riemann–Roch space of a divisor of negative degree vanishes, and it is cited by several results on degrees of principal divisors and on points of curves over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_sum_support.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem Divisor.degree_eq_sum_support {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by sorry
