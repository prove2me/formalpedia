-- Prove2me | Theorems.Thm_Algebra_mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual
-- name    : Algebra.mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/44488867-0370-53c2-b06f-343cae079879
-- title:
--   Different elements lie in ̄ x^{ n-1} on the special fibre
-- statement:
--   Let $R$ be a Noetherian integrally closed local domain with fraction field $K$, and let $S$ be an integrally closed domain which is a finite free $R$-algebra, with fraction field $F$, where $F$ is an $K$-algebra compatibly with the maps from $R$ and from $S$ and $F/K$ is separable. Let $\varpi \in R$ be nonzero such that $(\varpi)$ is prime, such that $R/(\varpi)$ is a discrete valuation ring and such that $\bar S := S/\varpi S$ is a Dedekind domain, and assume that every height-one prime $\mathfrak{Q}$ of $S$ containing $\varpi$ satisfies `Algebra.IsUnramifiedAt R 𝔔`. Let $s \in S$ be an element whose image in $F$ lies in $1 / \mathfrak{D}^{-1}$, where $\mathfrak{D}^{-1} = \operatorname{traceDual}_{R,K}(S)$ is the trace dual of $S$ inside $F$ and $1/(-)$ is the submodule quotient; equivalently, $s$ multiplies the trace dual into $S$. Let $x$ be a maximal ideal of $\bar S$ and $n$ a natural number such that the image in $\bar S$ of the maximal ideal of $R$ is contained in $x^{n}$. Then the image of $s$ in $\bar S$ lies in $x^{\,n-1}$ (truncated subtraction of naturals).
--
--   This is the statement that the different of $S/R$ bounds the ramification of the special fibre: an element of the different of the finite free extension $S/R$ reduces into $\bar x^{\,e-1}$ at each maximal ideal of the Dedekind fibre $\bar S$, the conclusion being phrased for every exponent $n$ with $\mathfrak m \bar S \subseteq x^{n}$ rather than for the ramification index itself. It feeds the existence and uniqueness statement [`Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing`](thm.html#Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem Algebra.mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (ϖ : R) (hϖ0 : ϖ ≠ 0) [hϖp : (Ideal.span ({ϖ} : Set R)).IsPrime] (hϖ : IsDiscreteValuationRing (R ⧸ Ideal.span ({ϖ} : Set R)))
    (hfib : IsDedekindDomain (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)))
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], algebraMap R S ϖ ∈ 𝔔 → 𝔔.height = 1 → Algebra.IsUnramifiedAt R 𝔔)
    (s : S) (hs : s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)))
    (x : Ideal (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) [x.IsMaximal]
    (n : ℕ) (hn : ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set R)))).map
      (algebraMap (R ⧸ Ideal.span ({ϖ} : Set R)) (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) ≤ x ^ n) :
    Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) s ∈ x ^ (n - 1) := by sorry
