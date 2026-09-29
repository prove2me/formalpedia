-- Prove2me | Theorems.Thm_Algebra_QuasiFiniteAt_exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective
-- name    : Algebra.QuasiFiniteAt.exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/ce9c6902-fbf8-5c76-8074-722bef1ab396
-- title:
--   Birational corollary of Zariski's main theorem
-- statement:
--   Let $R$ be an integrally closed commutative domain, $S$ a commutative ring and $K$ a field, with $R$-algebra structures on $S$ and on $K$ such that $K$ is a fraction field of $R$, together with an $S$-algebra structure on $K$ compatible with these (a scalar tower $R \to S \to K$). Assume that the structure map $S \to K$ is injective, so that $R \subseteq S \subseteq K$ up to the given maps, that $S$ is of finite type as an $R$-algebra, and that $\mathfrak Q$ is a prime ideal of $S$ at which the Mathlib predicate `Algebra.QuasiFiniteAt R 𝔔` holds, i.e. $S$ is quasi-finite over $R$ at $\mathfrak Q$. The conclusion is that for every $s \in S$ there are elements $a, b \in R$ with $b$ outside the contraction $\mathfrak Q \cap R$ (the preimage of $\mathfrak Q$ under $R \to S$) such that $b\,s = a$ holds in $S$, the products and images being taken through $R \to S$. Equivalently, $S$ is contained in the localisation of $R$ at the prime $\mathfrak Q \cap R$, viewed inside $K$.
--
--   This is the birational case of Zariski's main theorem: a finite-type extension of a normal domain inside its fraction field, quasi-finite at a prime, is dominated there by a localisation of the base. It is used in the affine-chart analysis of local rings of curves, in particular by [`AlgebraicGeometry.exists_localRing_eq_localization_of_affineModel_of_map_maximalIdeal_le_of_isIntegrallyClosed_ofPrime`](thm.html#AlgebraicGeometry.exists_localRing_eq_localization_of_affineModel_of_map_maximalIdeal_le_of_isIntegrallyClosed_ofPrime), [`AlgebraicGeometry.exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le`](thm.html#AlgebraicGeometry.exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le) and [`AlgebraicGeometry.mem_localRing_node_iff_exists_mul_eq_of_nodeChart_of_forall_not_dominates`](thm.html#AlgebraicGeometry.mem_localRing_node_iff_exists_mul_eq_of_nodeChart_of_forall_not_dominates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_QuasiFiniteAt_exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.QuasiFiniteAt.exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective
    {R S K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsScalarTower R S K]
    (hSK : Function.Injective (algebraMap S K)) [Algebra.FiniteType R S]
    (𝔔 : Ideal S) [𝔔.IsPrime] [Algebra.QuasiFiniteAt R 𝔔] :
    ∀ s : S, ∃ a b : R, b ∉ 𝔔.comap (algebraMap R S) ∧ algebraMap R S b * s = algebraMap R S a := by sorry
